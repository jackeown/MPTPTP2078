%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ra2S9nbdIh

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:51 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  291 (4316 expanded)
%              Number of leaves         :   46 (1286 expanded)
%              Depth                    :   25
%              Number of atoms          : 2736 (114178 expanded)
%              Number of equality atoms :  203 (5927 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X23 @ X21 )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('29',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32','35'])).

thf('37',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','43'])).

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

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('64',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('66',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','56','66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('81',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('82',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('83',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != X19 )
      | ( v1_partfun1 @ X20 @ X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('86',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v4_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
      | ( v1_partfun1 @ X20 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('93',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['80','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('102',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('103',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','103'])).

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

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('118',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112','115','118','119'])).

thf('121',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['106','120'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('123',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('126',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('127',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','127'])).

thf('129',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('131',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136'])).

thf('138',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','137'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('140',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('144',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['128','144'])).

thf('146',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['146'])).

thf('148',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('150',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

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

thf('152',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('153',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('158',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','158'])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('161',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('165',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','148','149','163','164'])).

thf('166',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('167',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('168',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('169',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','43'])).

thf('171',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('172',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('175',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('177',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('180',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('182',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['146'])).

thf('183',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','188'])).

thf('190',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('191',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('193',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('194',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('195',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('196',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192','193','198'])).

thf('200',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','199'])).

thf('201',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','200'])).

thf('202',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['202','203','204','205'])).

thf('207',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['146'])).

thf('209',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['207','208'])).

thf('210',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['165','209'])).

thf('211',plain,
    ( ( ( u1_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','210'])).

thf('212',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('213',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X23 @ X21 )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('214',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('216',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('217',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('218',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('221',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('222',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['218','219','220','221','222'])).

thf('224',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['215','223'])).

thf('225',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('226',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['141'])).

thf('230',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','228','229'])).

thf('231',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('232',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('234',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('235',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('236',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('238',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['232','233','236','237'])).

thf('239',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['211','238'])).

thf('240',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','239'])).

thf('241',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['13','241','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ra2S9nbdIh
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.22/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.22/1.45  % Solved by: fo/fo7.sh
% 1.22/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.45  % done 694 iterations in 0.982s
% 1.22/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.22/1.45  % SZS output start Refutation
% 1.22/1.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.22/1.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.22/1.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.22/1.45  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.22/1.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.22/1.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.22/1.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.22/1.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.22/1.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.22/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.22/1.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.22/1.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.22/1.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.22/1.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.22/1.45  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.22/1.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.22/1.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.22/1.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.22/1.45  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.22/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.22/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.22/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.22/1.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.22/1.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.22/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.22/1.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.22/1.45  thf(t62_tops_2, conjecture,
% 1.22/1.45    (![A:$i]:
% 1.22/1.45     ( ( l1_struct_0 @ A ) =>
% 1.22/1.45       ( ![B:$i]:
% 1.22/1.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.22/1.45           ( ![C:$i]:
% 1.22/1.45             ( ( ( v1_funct_1 @ C ) & 
% 1.22/1.45                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.22/1.45                 ( m1_subset_1 @
% 1.22/1.45                   C @ 
% 1.22/1.45                   ( k1_zfmisc_1 @
% 1.22/1.45                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.22/1.45               ( ( ( ( k2_relset_1 @
% 1.22/1.45                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.22/1.45                     ( k2_struct_0 @ B ) ) & 
% 1.22/1.45                   ( v2_funct_1 @ C ) ) =>
% 1.22/1.45                 ( ( ( k1_relset_1 @
% 1.22/1.45                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.22/1.45                       ( k2_tops_2 @
% 1.22/1.45                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.22/1.45                     ( k2_struct_0 @ B ) ) & 
% 1.22/1.45                   ( ( k2_relset_1 @
% 1.22/1.45                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.22/1.45                       ( k2_tops_2 @
% 1.22/1.45                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.22/1.45                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.22/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.45    (~( ![A:$i]:
% 1.22/1.45        ( ( l1_struct_0 @ A ) =>
% 1.22/1.45          ( ![B:$i]:
% 1.22/1.45            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.22/1.45              ( ![C:$i]:
% 1.22/1.45                ( ( ( v1_funct_1 @ C ) & 
% 1.22/1.45                    ( v1_funct_2 @
% 1.22/1.45                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.22/1.45                    ( m1_subset_1 @
% 1.22/1.45                      C @ 
% 1.22/1.45                      ( k1_zfmisc_1 @
% 1.22/1.45                        ( k2_zfmisc_1 @
% 1.22/1.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.22/1.45                  ( ( ( ( k2_relset_1 @
% 1.22/1.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.22/1.45                        ( k2_struct_0 @ B ) ) & 
% 1.22/1.45                      ( v2_funct_1 @ C ) ) =>
% 1.22/1.45                    ( ( ( k1_relset_1 @
% 1.22/1.45                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.22/1.45                          ( k2_tops_2 @
% 1.22/1.45                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.22/1.45                        ( k2_struct_0 @ B ) ) & 
% 1.22/1.45                      ( ( k2_relset_1 @
% 1.22/1.45                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.22/1.45                          ( k2_tops_2 @
% 1.22/1.45                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.22/1.45                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.22/1.45    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.22/1.45  thf('0', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf(redefinition_k2_relset_1, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.22/1.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.22/1.45  thf('1', plain,
% 1.22/1.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.22/1.45         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.22/1.45          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.22/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.22/1.45  thf('2', plain,
% 1.22/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['0', '1'])).
% 1.22/1.45  thf('3', plain,
% 1.22/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf(d3_struct_0, axiom,
% 1.22/1.45    (![A:$i]:
% 1.22/1.45     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.22/1.45  thf('5', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf(fc2_struct_0, axiom,
% 1.22/1.45    (![A:$i]:
% 1.22/1.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.22/1.45       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.22/1.45  thf('6', plain,
% 1.22/1.45      (![X28 : $i]:
% 1.22/1.45         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 1.22/1.45          | ~ (l1_struct_0 @ X28)
% 1.22/1.45          | (v2_struct_0 @ X28))),
% 1.22/1.45      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.22/1.45  thf('7', plain,
% 1.22/1.45      (![X0 : $i]:
% 1.22/1.45         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.22/1.45          | ~ (l1_struct_0 @ X0)
% 1.22/1.45          | (v2_struct_0 @ X0)
% 1.22/1.45          | ~ (l1_struct_0 @ X0))),
% 1.22/1.45      inference('sup-', [status(thm)], ['5', '6'])).
% 1.22/1.45  thf('8', plain,
% 1.22/1.45      (![X0 : $i]:
% 1.22/1.45         ((v2_struct_0 @ X0)
% 1.22/1.45          | ~ (l1_struct_0 @ X0)
% 1.22/1.45          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.22/1.45      inference('simplify', [status(thm)], ['7'])).
% 1.22/1.45  thf('9', plain,
% 1.22/1.45      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.22/1.45        | (v2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup-', [status(thm)], ['4', '8'])).
% 1.22/1.45  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('11', plain,
% 1.22/1.45      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['9', '10'])).
% 1.22/1.45  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('clc', [status(thm)], ['11', '12'])).
% 1.22/1.45  thf('14', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('15', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('16', plain,
% 1.22/1.45      (((m1_subset_1 @ sk_C @ 
% 1.22/1.45         (k1_zfmisc_1 @ 
% 1.22/1.45          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['14', '15'])).
% 1.22/1.45  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('18', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.22/1.45      inference('demod', [status(thm)], ['16', '17'])).
% 1.22/1.45  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('20', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.22/1.45      inference('demod', [status(thm)], ['18', '19'])).
% 1.22/1.45  thf('21', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf(t132_funct_2, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( ( v1_funct_1 @ C ) & 
% 1.22/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.22/1.45       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.22/1.45           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.22/1.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.22/1.45           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.22/1.45  thf('22', plain,
% 1.22/1.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.22/1.45         (((X21) = (k1_xboole_0))
% 1.22/1.45          | ~ (v1_funct_1 @ X22)
% 1.22/1.45          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 1.22/1.45          | (v1_partfun1 @ X22 @ X23)
% 1.22/1.45          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 1.22/1.45          | ~ (v1_funct_2 @ X22 @ X23 @ X21)
% 1.22/1.45          | ~ (v1_funct_1 @ X22))),
% 1.22/1.45      inference('cnf', [status(esa)], [t132_funct_2])).
% 1.22/1.45  thf('23', plain,
% 1.22/1.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.22/1.45         (~ (v1_funct_2 @ X22 @ X23 @ X21)
% 1.22/1.45          | (v1_partfun1 @ X22 @ X23)
% 1.22/1.45          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 1.22/1.45          | ~ (v1_funct_1 @ X22)
% 1.22/1.45          | ((X21) = (k1_xboole_0)))),
% 1.22/1.45      inference('simplify', [status(thm)], ['22'])).
% 1.22/1.45  thf('24', plain,
% 1.22/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.22/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.22/1.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['21', '23'])).
% 1.22/1.45  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('26', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('27', plain,
% 1.22/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.22/1.45        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.22/1.45      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.22/1.45  thf(d4_partfun1, axiom,
% 1.22/1.45    (![A:$i,B:$i]:
% 1.22/1.45     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.22/1.45       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.22/1.45  thf('28', plain,
% 1.22/1.45      (![X19 : $i, X20 : $i]:
% 1.22/1.45         (~ (v1_partfun1 @ X20 @ X19)
% 1.22/1.45          | ((k1_relat_1 @ X20) = (X19))
% 1.22/1.45          | ~ (v4_relat_1 @ X20 @ X19)
% 1.22/1.45          | ~ (v1_relat_1 @ X20))),
% 1.22/1.45      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.22/1.45  thf('29', plain,
% 1.22/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.22/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.22/1.45        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.22/1.45        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['27', '28'])).
% 1.22/1.45  thf('30', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf(cc1_relset_1, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.22/1.45       ( v1_relat_1 @ C ) ))).
% 1.22/1.45  thf('31', plain,
% 1.22/1.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.45         ((v1_relat_1 @ X2)
% 1.22/1.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.22/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.22/1.45  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 1.22/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.22/1.45  thf('33', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf(cc2_relset_1, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.22/1.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.22/1.45  thf('34', plain,
% 1.22/1.45      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.22/1.45         ((v4_relat_1 @ X5 @ X6)
% 1.22/1.45          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.22/1.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.22/1.45  thf('35', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('sup-', [status(thm)], ['33', '34'])).
% 1.22/1.45  thf('36', plain,
% 1.22/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.22/1.45        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.22/1.45      inference('demod', [status(thm)], ['29', '32', '35'])).
% 1.22/1.45  thf('37', plain,
% 1.22/1.45      (![X28 : $i]:
% 1.22/1.45         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 1.22/1.45          | ~ (l1_struct_0 @ X28)
% 1.22/1.45          | (v2_struct_0 @ X28))),
% 1.22/1.45      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.22/1.45  thf('38', plain,
% 1.22/1.45      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.22/1.45        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 1.22/1.45        | (v2_struct_0 @ sk_B)
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup-', [status(thm)], ['36', '37'])).
% 1.22/1.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.22/1.45  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.22/1.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.22/1.45  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('41', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.22/1.45  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('43', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('44', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.22/1.45      inference('demod', [status(thm)], ['20', '43'])).
% 1.22/1.45  thf(t31_funct_2, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.22/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.22/1.45       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.22/1.45         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.22/1.45           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.22/1.45           ( m1_subset_1 @
% 1.22/1.45             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.22/1.45  thf('45', plain,
% 1.22/1.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X24)
% 1.22/1.45          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.22/1.45          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 1.22/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.22/1.45          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.22/1.45          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.22/1.45          | ~ (v1_funct_1 @ X24))),
% 1.22/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.22/1.45  thf('46', plain,
% 1.22/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.22/1.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45           (k1_zfmisc_1 @ 
% 1.22/1.45            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.22/1.45        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45            != (k2_relat_1 @ sk_C))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['44', '45'])).
% 1.22/1.45  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('48', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('49', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('50', plain,
% 1.22/1.45      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['48', '49'])).
% 1.22/1.45  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('52', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['50', '51'])).
% 1.22/1.45  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('54', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['52', '53'])).
% 1.22/1.45  thf('55', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('56', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['54', '55'])).
% 1.22/1.45  thf('57', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('58', plain,
% 1.22/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('59', plain,
% 1.22/1.45      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45          = (k2_struct_0 @ sk_B))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['57', '58'])).
% 1.22/1.45  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('61', plain,
% 1.22/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['59', '60'])).
% 1.22/1.45  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('64', plain,
% 1.22/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.22/1.45  thf('65', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('66', plain,
% 1.22/1.45      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['64', '65'])).
% 1.22/1.45  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('68', plain,
% 1.22/1.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45         (k1_zfmisc_1 @ 
% 1.22/1.45          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.22/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.22/1.45      inference('demod', [status(thm)], ['46', '47', '56', '66', '67'])).
% 1.22/1.45  thf('69', plain,
% 1.22/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.22/1.45      inference('simplify', [status(thm)], ['68'])).
% 1.22/1.45  thf('70', plain,
% 1.22/1.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.45         ((v1_relat_1 @ X2)
% 1.22/1.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.22/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.22/1.45  thf('71', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['69', '70'])).
% 1.22/1.45  thf(t55_funct_1, axiom,
% 1.22/1.45    (![A:$i]:
% 1.22/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.22/1.45       ( ( v2_funct_1 @ A ) =>
% 1.22/1.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.22/1.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.22/1.45  thf('72', plain,
% 1.22/1.45      (![X1 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X1)
% 1.22/1.45          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.22/1.45          | ~ (v1_funct_1 @ X1)
% 1.22/1.45          | ~ (v1_relat_1 @ X1))),
% 1.22/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.22/1.45  thf(t65_relat_1, axiom,
% 1.22/1.45    (![A:$i]:
% 1.22/1.45     ( ( v1_relat_1 @ A ) =>
% 1.22/1.45       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.22/1.45         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.22/1.45  thf('73', plain,
% 1.22/1.45      (![X0 : $i]:
% 1.22/1.45         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.22/1.45          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 1.22/1.45          | ~ (v1_relat_1 @ X0))),
% 1.22/1.45      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.22/1.45  thf('74', plain,
% 1.22/1.45      (![X0 : $i]:
% 1.22/1.45         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 1.22/1.45          | ~ (v1_relat_1 @ X0)
% 1.22/1.45          | ~ (v1_funct_1 @ X0)
% 1.22/1.45          | ~ (v2_funct_1 @ X0)
% 1.22/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.22/1.45          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['72', '73'])).
% 1.22/1.45  thf('75', plain,
% 1.22/1.45      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.22/1.45        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['71', '74'])).
% 1.22/1.45  thf('76', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 1.22/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.22/1.45  thf('79', plain,
% 1.22/1.45      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))
% 1.22/1.45        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.22/1.45      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.22/1.45  thf('80', plain,
% 1.22/1.45      (![X1 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X1)
% 1.22/1.45          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.22/1.45          | ~ (v1_funct_1 @ X1)
% 1.22/1.45          | ~ (v1_relat_1 @ X1))),
% 1.22/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.22/1.45  thf('81', plain,
% 1.22/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.22/1.45      inference('simplify', [status(thm)], ['68'])).
% 1.22/1.45  thf('82', plain,
% 1.22/1.45      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.22/1.45         ((v4_relat_1 @ X5 @ X6)
% 1.22/1.45          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.22/1.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.22/1.45  thf('83', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['81', '82'])).
% 1.22/1.45  thf('84', plain,
% 1.22/1.45      (![X1 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X1)
% 1.22/1.45          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.22/1.45          | ~ (v1_funct_1 @ X1)
% 1.22/1.45          | ~ (v1_relat_1 @ X1))),
% 1.22/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.22/1.45  thf('85', plain,
% 1.22/1.45      (![X19 : $i, X20 : $i]:
% 1.22/1.45         (((k1_relat_1 @ X20) != (X19))
% 1.22/1.45          | (v1_partfun1 @ X20 @ X19)
% 1.22/1.45          | ~ (v4_relat_1 @ X20 @ X19)
% 1.22/1.45          | ~ (v1_relat_1 @ X20))),
% 1.22/1.45      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.22/1.45  thf('86', plain,
% 1.22/1.45      (![X20 : $i]:
% 1.22/1.45         (~ (v1_relat_1 @ X20)
% 1.22/1.45          | ~ (v4_relat_1 @ X20 @ (k1_relat_1 @ X20))
% 1.22/1.45          | (v1_partfun1 @ X20 @ (k1_relat_1 @ X20)))),
% 1.22/1.45      inference('simplify', [status(thm)], ['85'])).
% 1.22/1.45  thf('87', plain,
% 1.22/1.45      (![X0 : $i]:
% 1.22/1.45         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.22/1.45          | ~ (v1_relat_1 @ X0)
% 1.22/1.45          | ~ (v1_funct_1 @ X0)
% 1.22/1.45          | ~ (v2_funct_1 @ X0)
% 1.22/1.45          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.22/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['84', '86'])).
% 1.22/1.45  thf('88', plain,
% 1.22/1.45      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.22/1.45        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_relat_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['83', '87'])).
% 1.22/1.45  thf('89', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['69', '70'])).
% 1.22/1.45  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 1.22/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.22/1.45  thf('93', plain,
% 1.22/1.45      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.22/1.45      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 1.22/1.45  thf('94', plain,
% 1.22/1.45      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.22/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup+', [status(thm)], ['80', '93'])).
% 1.22/1.45  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 1.22/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.22/1.45  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('98', plain, ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 1.22/1.45  thf('99', plain,
% 1.22/1.45      (![X19 : $i, X20 : $i]:
% 1.22/1.45         (~ (v1_partfun1 @ X20 @ X19)
% 1.22/1.45          | ((k1_relat_1 @ X20) = (X19))
% 1.22/1.45          | ~ (v4_relat_1 @ X20 @ X19)
% 1.22/1.45          | ~ (v1_relat_1 @ X20))),
% 1.22/1.45      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.22/1.45  thf('100', plain,
% 1.22/1.45      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.22/1.45        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.22/1.45        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['98', '99'])).
% 1.22/1.45  thf('101', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['69', '70'])).
% 1.22/1.45  thf('102', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['81', '82'])).
% 1.22/1.45  thf('103', plain,
% 1.22/1.45      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.22/1.45  thf('104', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | ((k1_relat_1 @ sk_C) != (k1_xboole_0)))),
% 1.22/1.45      inference('demod', [status(thm)], ['79', '103'])).
% 1.22/1.45  thf(d1_funct_2, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.22/1.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.22/1.45           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.22/1.45             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.22/1.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.22/1.45           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.22/1.45             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.22/1.45  thf(zf_stmt_1, axiom,
% 1.22/1.45    (![B:$i,A:$i]:
% 1.22/1.45     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.22/1.45       ( zip_tseitin_0 @ B @ A ) ))).
% 1.22/1.45  thf('105', plain,
% 1.22/1.45      (![X11 : $i, X12 : $i]:
% 1.22/1.45         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.22/1.45  thf('106', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('107', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('108', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('109', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('demod', [status(thm)], ['107', '108'])).
% 1.22/1.45  thf('110', plain,
% 1.22/1.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X24)
% 1.22/1.45          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.22/1.45          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 1.22/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.22/1.45          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.22/1.45          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.22/1.45          | ~ (v1_funct_1 @ X24))),
% 1.22/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.22/1.45  thf('111', plain,
% 1.22/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.22/1.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45           (k1_zfmisc_1 @ 
% 1.22/1.45            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.22/1.45        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45            != (u1_struct_0 @ sk_B))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['109', '110'])).
% 1.22/1.45  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('113', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('114', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('115', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['113', '114'])).
% 1.22/1.45  thf('116', plain,
% 1.22/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['0', '1'])).
% 1.22/1.45  thf('117', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('118', plain,
% 1.22/1.45      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['116', '117'])).
% 1.22/1.45  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('120', plain,
% 1.22/1.45      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45         (k1_zfmisc_1 @ 
% 1.22/1.45          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.22/1.45        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('demod', [status(thm)], ['111', '112', '115', '118', '119'])).
% 1.22/1.45  thf('121', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.22/1.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45           (k1_zfmisc_1 @ 
% 1.22/1.45            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['106', '120'])).
% 1.22/1.45  thf('122', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('123', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('124', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.22/1.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45           (k1_zfmisc_1 @ 
% 1.22/1.45            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.22/1.45      inference('demod', [status(thm)], ['121', '122', '123'])).
% 1.22/1.45  thf('125', plain,
% 1.22/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.22/1.45      inference('simplify', [status(thm)], ['124'])).
% 1.22/1.45  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.22/1.45  thf(zf_stmt_3, axiom,
% 1.22/1.45    (![C:$i,B:$i,A:$i]:
% 1.22/1.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.22/1.45       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.22/1.45  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.22/1.45  thf(zf_stmt_5, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.22/1.45       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.22/1.45         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.22/1.45           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.22/1.45             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.22/1.45  thf('126', plain,
% 1.22/1.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.22/1.45         (~ (zip_tseitin_0 @ X16 @ X17)
% 1.22/1.45          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 1.22/1.45          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.22/1.45  thf('127', plain,
% 1.22/1.45      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45         (u1_struct_0 @ sk_B))
% 1.22/1.45        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['125', '126'])).
% 1.22/1.45  thf('128', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45           (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['105', '127'])).
% 1.22/1.45  thf('129', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('130', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('demod', [status(thm)], ['107', '108'])).
% 1.22/1.45  thf('131', plain,
% 1.22/1.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X24)
% 1.22/1.45          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.22/1.45          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 1.22/1.45          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.22/1.45          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.22/1.45          | ~ (v1_funct_1 @ X24))),
% 1.22/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.22/1.45  thf('132', plain,
% 1.22/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.22/1.45        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.22/1.45           (k1_relat_1 @ sk_C))
% 1.22/1.45        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45            != (u1_struct_0 @ sk_B))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['130', '131'])).
% 1.22/1.45  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('134', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['113', '114'])).
% 1.22/1.45  thf('135', plain,
% 1.22/1.45      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['116', '117'])).
% 1.22/1.45  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('137', plain,
% 1.22/1.45      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.22/1.45         (k1_relat_1 @ sk_C))
% 1.22/1.45        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('demod', [status(thm)], ['132', '133', '134', '135', '136'])).
% 1.22/1.45  thf('138', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.22/1.45        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.22/1.45           (k1_relat_1 @ sk_C)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['129', '137'])).
% 1.22/1.45  thf('139', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('140', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('141', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.22/1.45        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.22/1.45           (k1_relat_1 @ sk_C)))),
% 1.22/1.45      inference('demod', [status(thm)], ['138', '139', '140'])).
% 1.22/1.45  thf('142', plain,
% 1.22/1.45      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.22/1.45        (k1_relat_1 @ sk_C))),
% 1.22/1.45      inference('simplify', [status(thm)], ['141'])).
% 1.22/1.45  thf('143', plain,
% 1.22/1.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.22/1.45         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 1.22/1.45          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 1.22/1.45          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.22/1.45  thf('144', plain,
% 1.22/1.45      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45           (u1_struct_0 @ sk_B))
% 1.22/1.45        | ((u1_struct_0 @ sk_B)
% 1.22/1.45            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45               (k2_funct_1 @ sk_C))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['142', '143'])).
% 1.22/1.45  thf('145', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | ((u1_struct_0 @ sk_B)
% 1.22/1.45            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45               (k2_funct_1 @ sk_C))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['128', '144'])).
% 1.22/1.45  thf('146', plain,
% 1.22/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          != (k2_struct_0 @ sk_B))
% 1.22/1.45        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45            != (k2_struct_0 @ sk_A)))),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('147', plain,
% 1.22/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          != (k2_struct_0 @ sk_B)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_B))))),
% 1.22/1.45      inference('split', [status(esa)], ['146'])).
% 1.22/1.45  thf('148', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('149', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('150', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('151', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('demod', [status(thm)], ['107', '108'])).
% 1.22/1.45  thf(d4_tops_2, axiom,
% 1.22/1.45    (![A:$i,B:$i,C:$i]:
% 1.22/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.22/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.22/1.45       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.22/1.45         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.22/1.45  thf('152', plain,
% 1.22/1.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.22/1.45         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 1.22/1.45          | ~ (v2_funct_1 @ X31)
% 1.22/1.45          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 1.22/1.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.22/1.45          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 1.22/1.45          | ~ (v1_funct_1 @ X31))),
% 1.22/1.45      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.22/1.45  thf('153', plain,
% 1.22/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.22/1.45        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45            = (k2_funct_1 @ sk_C))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.22/1.45        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45            != (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['151', '152'])).
% 1.22/1.45  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('155', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['113', '114'])).
% 1.22/1.45  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('157', plain,
% 1.22/1.45      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['116', '117'])).
% 1.22/1.45  thf('158', plain,
% 1.22/1.45      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45          = (k2_funct_1 @ sk_C))
% 1.22/1.45        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 1.22/1.45  thf('159', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.22/1.45        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45            = (k2_funct_1 @ sk_C)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['150', '158'])).
% 1.22/1.45  thf('160', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('161', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('162', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.22/1.45        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45            = (k2_funct_1 @ sk_C)))),
% 1.22/1.45      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.22/1.45  thf('163', plain,
% 1.22/1.45      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_funct_1 @ sk_C))),
% 1.22/1.45      inference('simplify', [status(thm)], ['162'])).
% 1.22/1.45  thf('164', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('165', plain,
% 1.22/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_B))))),
% 1.22/1.45      inference('demod', [status(thm)], ['147', '148', '149', '163', '164'])).
% 1.22/1.45  thf('166', plain,
% 1.22/1.45      (![X1 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X1)
% 1.22/1.45          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.22/1.45          | ~ (v1_funct_1 @ X1)
% 1.22/1.45          | ~ (v1_relat_1 @ X1))),
% 1.22/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.22/1.45  thf('167', plain,
% 1.22/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.22/1.45      inference('simplify', [status(thm)], ['68'])).
% 1.22/1.45  thf('168', plain,
% 1.22/1.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.22/1.45         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.22/1.45          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.22/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.22/1.45  thf('169', plain,
% 1.22/1.45      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['167', '168'])).
% 1.22/1.45  thf('170', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.22/1.45      inference('demod', [status(thm)], ['20', '43'])).
% 1.22/1.45  thf('171', plain,
% 1.22/1.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.22/1.45         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 1.22/1.45          | ~ (v2_funct_1 @ X31)
% 1.22/1.45          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 1.22/1.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 1.22/1.45          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 1.22/1.45          | ~ (v1_funct_1 @ X31))),
% 1.22/1.45      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.22/1.45  thf('172', plain,
% 1.22/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.22/1.45        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45            = (k2_funct_1 @ sk_C))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.22/1.45        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45            != (k2_relat_1 @ sk_C)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['170', '171'])).
% 1.22/1.45  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('174', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['54', '55'])).
% 1.22/1.45  thf('175', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('176', plain,
% 1.22/1.45      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['64', '65'])).
% 1.22/1.45  thf('177', plain,
% 1.22/1.45      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45          = (k2_funct_1 @ sk_C))
% 1.22/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.22/1.45      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 1.22/1.45  thf('178', plain,
% 1.22/1.45      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.22/1.45         = (k2_funct_1 @ sk_C))),
% 1.22/1.45      inference('simplify', [status(thm)], ['177'])).
% 1.22/1.45  thf('179', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('180', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('181', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('182', plain,
% 1.22/1.45      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          != (k2_struct_0 @ sk_A)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('split', [status(esa)], ['146'])).
% 1.22/1.45  thf('183', plain,
% 1.22/1.45      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45           != (k2_struct_0 @ sk_A))
% 1.22/1.45         | ~ (l1_struct_0 @ sk_B)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['181', '182'])).
% 1.22/1.45  thf('184', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('185', plain,
% 1.22/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          != (k2_struct_0 @ sk_A)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('demod', [status(thm)], ['183', '184'])).
% 1.22/1.45  thf('186', plain,
% 1.22/1.45      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45           != (k2_struct_0 @ sk_A))
% 1.22/1.45         | ~ (l1_struct_0 @ sk_B)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['180', '185'])).
% 1.22/1.45  thf('187', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('188', plain,
% 1.22/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          != (k2_struct_0 @ sk_A)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('demod', [status(thm)], ['186', '187'])).
% 1.22/1.45  thf('189', plain,
% 1.22/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.22/1.45          != (k2_struct_0 @ sk_A)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['179', '188'])).
% 1.22/1.45  thf('190', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('191', plain,
% 1.22/1.45      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.22/1.45          != (k2_struct_0 @ sk_A)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('demod', [status(thm)], ['189', '190'])).
% 1.22/1.45  thf('192', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('193', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('194', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('195', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.22/1.45      inference('clc', [status(thm)], ['41', '42'])).
% 1.22/1.45  thf('196', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.22/1.45      inference('sup+', [status(thm)], ['194', '195'])).
% 1.22/1.45  thf('197', plain, ((l1_struct_0 @ sk_A)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('198', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.22/1.45      inference('demod', [status(thm)], ['196', '197'])).
% 1.22/1.45  thf('199', plain,
% 1.22/1.45      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.22/1.45          != (k1_relat_1 @ sk_C)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('demod', [status(thm)], ['191', '192', '193', '198'])).
% 1.22/1.45  thf('200', plain,
% 1.22/1.45      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['178', '199'])).
% 1.22/1.45  thf('201', plain,
% 1.22/1.45      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['169', '200'])).
% 1.22/1.45  thf('202', plain,
% 1.22/1.45      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.22/1.45         | ~ (v1_relat_1 @ sk_C)
% 1.22/1.45         | ~ (v1_funct_1 @ sk_C)
% 1.22/1.45         | ~ (v2_funct_1 @ sk_C)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('sup-', [status(thm)], ['166', '201'])).
% 1.22/1.45  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 1.22/1.45      inference('sup-', [status(thm)], ['30', '31'])).
% 1.22/1.45  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('205', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('206', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.22/1.45         <= (~
% 1.22/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45                = (k2_struct_0 @ sk_A))))),
% 1.22/1.45      inference('demod', [status(thm)], ['202', '203', '204', '205'])).
% 1.22/1.45  thf('207', plain,
% 1.22/1.45      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          = (k2_struct_0 @ sk_A)))),
% 1.22/1.45      inference('simplify', [status(thm)], ['206'])).
% 1.22/1.45  thf('208', plain,
% 1.22/1.45      (~
% 1.22/1.45       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          = (k2_struct_0 @ sk_B))) | 
% 1.22/1.45       ~
% 1.22/1.45       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          = (k2_struct_0 @ sk_A)))),
% 1.22/1.45      inference('split', [status(esa)], ['146'])).
% 1.22/1.45  thf('209', plain,
% 1.22/1.45      (~
% 1.22/1.45       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.22/1.45          = (k2_struct_0 @ sk_B)))),
% 1.22/1.45      inference('sat_resolution*', [status(thm)], ['207', '208'])).
% 1.22/1.45  thf('210', plain,
% 1.22/1.45      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.22/1.45         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('simpl_trail', [status(thm)], ['165', '209'])).
% 1.22/1.45  thf('211', plain,
% 1.22/1.45      ((((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 1.22/1.45        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['145', '210'])).
% 1.22/1.45  thf('212', plain,
% 1.22/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.22/1.45      inference('simplify', [status(thm)], ['124'])).
% 1.22/1.45  thf('213', plain,
% 1.22/1.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.22/1.45         (~ (v1_funct_2 @ X22 @ X23 @ X21)
% 1.22/1.45          | (v1_partfun1 @ X22 @ X23)
% 1.22/1.45          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 1.22/1.45          | ~ (v1_funct_1 @ X22)
% 1.22/1.45          | ((X21) = (k1_xboole_0)))),
% 1.22/1.45      inference('simplify', [status(thm)], ['22'])).
% 1.22/1.45  thf('214', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.22/1.45        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.22/1.45        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.22/1.45             (k1_relat_1 @ sk_C)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['212', '213'])).
% 1.22/1.45  thf('215', plain,
% 1.22/1.45      (![X27 : $i]:
% 1.22/1.45         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 1.22/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.22/1.45  thf('216', plain,
% 1.22/1.45      ((m1_subset_1 @ sk_C @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.22/1.45      inference('demod', [status(thm)], ['107', '108'])).
% 1.22/1.45  thf('217', plain,
% 1.22/1.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.22/1.45         (~ (v2_funct_1 @ X24)
% 1.22/1.45          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 1.22/1.45          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 1.22/1.45          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.22/1.45          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 1.22/1.45          | ~ (v1_funct_1 @ X24))),
% 1.22/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.22/1.45  thf('218', plain,
% 1.22/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.22/1.45        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.22/1.45        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.22/1.45        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45            != (u1_struct_0 @ sk_B))
% 1.22/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['216', '217'])).
% 1.22/1.45  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('220', plain,
% 1.22/1.45      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('demod', [status(thm)], ['113', '114'])).
% 1.22/1.45  thf('221', plain,
% 1.22/1.45      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.22/1.45         = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['116', '117'])).
% 1.22/1.45  thf('222', plain, ((v2_funct_1 @ sk_C)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('223', plain,
% 1.22/1.45      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.22/1.45        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('demod', [status(thm)], ['218', '219', '220', '221', '222'])).
% 1.22/1.45  thf('224', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.22/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.22/1.45        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['215', '223'])).
% 1.22/1.45  thf('225', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup+', [status(thm)], ['2', '3'])).
% 1.22/1.45  thf('226', plain, ((l1_struct_0 @ sk_B)),
% 1.22/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.45  thf('227', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.22/1.45        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.22/1.45      inference('demod', [status(thm)], ['224', '225', '226'])).
% 1.22/1.45  thf('228', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.22/1.45      inference('simplify', [status(thm)], ['227'])).
% 1.22/1.45  thf('229', plain,
% 1.22/1.45      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.22/1.45        (k1_relat_1 @ sk_C))),
% 1.22/1.45      inference('simplify', [status(thm)], ['141'])).
% 1.22/1.45  thf('230', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('demod', [status(thm)], ['214', '228', '229'])).
% 1.22/1.45  thf('231', plain,
% 1.22/1.45      (![X19 : $i, X20 : $i]:
% 1.22/1.45         (~ (v1_partfun1 @ X20 @ X19)
% 1.22/1.45          | ((k1_relat_1 @ X20) = (X19))
% 1.22/1.45          | ~ (v4_relat_1 @ X20 @ X19)
% 1.22/1.45          | ~ (v1_relat_1 @ X20))),
% 1.22/1.45      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.22/1.45  thf('232', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.22/1.45        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.22/1.45        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('sup-', [status(thm)], ['230', '231'])).
% 1.22/1.45  thf('233', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.22/1.45      inference('sup-', [status(thm)], ['69', '70'])).
% 1.22/1.45  thf('234', plain,
% 1.22/1.45      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.22/1.45        (k1_zfmisc_1 @ 
% 1.22/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.22/1.45      inference('simplify', [status(thm)], ['124'])).
% 1.22/1.45  thf('235', plain,
% 1.22/1.45      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.22/1.45         ((v4_relat_1 @ X5 @ X6)
% 1.22/1.45          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.22/1.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.22/1.45  thf('236', plain,
% 1.22/1.45      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.22/1.45      inference('sup-', [status(thm)], ['234', '235'])).
% 1.22/1.45  thf('237', plain,
% 1.22/1.45      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.22/1.45      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.22/1.45  thf('238', plain,
% 1.22/1.45      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | ((k2_relat_1 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 1.22/1.45      inference('demod', [status(thm)], ['232', '233', '236', '237'])).
% 1.22/1.45  thf('239', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.22/1.45      inference('clc', [status(thm)], ['211', '238'])).
% 1.22/1.45  thf('240', plain,
% 1.22/1.45      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.22/1.45        | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.22/1.45      inference('demod', [status(thm)], ['104', '239'])).
% 1.22/1.45  thf('241', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.22/1.45      inference('simplify', [status(thm)], ['240'])).
% 1.22/1.45  thf('242', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.22/1.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.22/1.45  thf('243', plain, ($false),
% 1.22/1.45      inference('demod', [status(thm)], ['13', '241', '242'])).
% 1.22/1.45  
% 1.22/1.45  % SZS output end Refutation
% 1.22/1.45  
% 1.30/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
