%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lXIbBnHmBr

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:03 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 352 expanded)
%              Number of leaves         :   41 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          : 1124 (9253 expanded)
%              Number of equality atoms :   88 ( 518 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('45',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('52',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('53',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','50','51','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','70','71'])).

thf('73',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['62','72'])).

thf('74',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','73'])).

thf('75',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('77',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('78',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','84'])).

thf('86',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','86'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['13','87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lXIbBnHmBr
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.92  % Solved by: fo/fo7.sh
% 0.69/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.92  % done 369 iterations in 0.460s
% 0.69/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.92  % SZS output start Refutation
% 0.69/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.69/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.69/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.69/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.92  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.69/0.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.69/0.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.69/0.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.92  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.69/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.69/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.92  thf(t62_tops_2, conjecture,
% 0.69/0.92    (![A:$i]:
% 0.69/0.92     ( ( l1_struct_0 @ A ) =>
% 0.69/0.92       ( ![B:$i]:
% 0.69/0.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.69/0.92           ( ![C:$i]:
% 0.69/0.92             ( ( ( v1_funct_1 @ C ) & 
% 0.69/0.92                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.92                 ( m1_subset_1 @
% 0.69/0.92                   C @ 
% 0.69/0.92                   ( k1_zfmisc_1 @
% 0.69/0.92                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.92               ( ( ( ( k2_relset_1 @
% 0.69/0.92                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.69/0.92                     ( k2_struct_0 @ B ) ) & 
% 0.69/0.92                   ( v2_funct_1 @ C ) ) =>
% 0.69/0.92                 ( ( ( k1_relset_1 @
% 0.69/0.92                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.69/0.92                       ( k2_tops_2 @
% 0.69/0.92                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.69/0.92                     ( k2_struct_0 @ B ) ) & 
% 0.69/0.92                   ( ( k2_relset_1 @
% 0.69/0.92                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.69/0.92                       ( k2_tops_2 @
% 0.69/0.92                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.69/0.92                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.69/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.92    (~( ![A:$i]:
% 0.69/0.92        ( ( l1_struct_0 @ A ) =>
% 0.69/0.92          ( ![B:$i]:
% 0.69/0.92            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.69/0.92              ( ![C:$i]:
% 0.69/0.92                ( ( ( v1_funct_1 @ C ) & 
% 0.69/0.92                    ( v1_funct_2 @
% 0.69/0.92                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.69/0.92                    ( m1_subset_1 @
% 0.69/0.92                      C @ 
% 0.69/0.92                      ( k1_zfmisc_1 @
% 0.69/0.92                        ( k2_zfmisc_1 @
% 0.69/0.92                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.69/0.92                  ( ( ( ( k2_relset_1 @
% 0.69/0.92                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.69/0.92                        ( k2_struct_0 @ B ) ) & 
% 0.69/0.92                      ( v2_funct_1 @ C ) ) =>
% 0.69/0.92                    ( ( ( k1_relset_1 @
% 0.69/0.92                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.69/0.92                          ( k2_tops_2 @
% 0.69/0.92                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.69/0.92                        ( k2_struct_0 @ B ) ) & 
% 0.69/0.92                      ( ( k2_relset_1 @
% 0.69/0.92                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.69/0.92                          ( k2_tops_2 @
% 0.69/0.92                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.69/0.92                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.69/0.92    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.69/0.92  thf('0', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_C @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(redefinition_k2_relset_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.92       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.69/0.92  thf('1', plain,
% 0.69/0.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.92         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.69/0.92          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.69/0.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.92  thf('2', plain,
% 0.69/0.92      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92         = (k2_relat_1 @ sk_C))),
% 0.69/0.92      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.92  thf('3', plain,
% 0.69/0.92      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92         = (k2_struct_0 @ sk_B))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.69/0.92      inference('sup+', [status(thm)], ['2', '3'])).
% 0.69/0.92  thf(d3_struct_0, axiom,
% 0.69/0.92    (![A:$i]:
% 0.69/0.92     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.69/0.92  thf('5', plain,
% 0.69/0.92      (![X19 : $i]:
% 0.69/0.92         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.92  thf(fc2_struct_0, axiom,
% 0.69/0.92    (![A:$i]:
% 0.69/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.69/0.92       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.69/0.92  thf('6', plain,
% 0.69/0.92      (![X20 : $i]:
% 0.69/0.92         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 0.69/0.92          | ~ (l1_struct_0 @ X20)
% 0.69/0.92          | (v2_struct_0 @ X20))),
% 0.69/0.92      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.69/0.92  thf('7', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.69/0.92          | ~ (l1_struct_0 @ X0)
% 0.69/0.92          | (v2_struct_0 @ X0)
% 0.69/0.92          | ~ (l1_struct_0 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.92  thf('8', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         ((v2_struct_0 @ X0)
% 0.69/0.92          | ~ (l1_struct_0 @ X0)
% 0.69/0.92          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['7'])).
% 0.69/0.92  thf('9', plain,
% 0.69/0.92      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.69/0.92        | ~ (l1_struct_0 @ sk_B)
% 0.69/0.92        | (v2_struct_0 @ sk_B))),
% 0.69/0.92      inference('sup-', [status(thm)], ['4', '8'])).
% 0.69/0.92  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('11', plain,
% 0.69/0.92      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.69/0.92      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.92  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.69/0.92      inference('clc', [status(thm)], ['11', '12'])).
% 0.69/0.92  thf('14', plain,
% 0.69/0.92      (![X19 : $i]:
% 0.69/0.92         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.92  thf('15', plain,
% 0.69/0.92      (![X19 : $i]:
% 0.69/0.92         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.92  thf(d1_funct_2, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.69/0.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.69/0.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.69/0.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.92  thf(zf_stmt_1, axiom,
% 0.69/0.92    (![B:$i,A:$i]:
% 0.69/0.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.92       ( zip_tseitin_0 @ B @ A ) ))).
% 0.69/0.92  thf('16', plain,
% 0.69/0.92      (![X11 : $i, X12 : $i]:
% 0.69/0.92         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.92  thf('17', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_C @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.92  thf(zf_stmt_3, axiom,
% 0.69/0.92    (![C:$i,B:$i,A:$i]:
% 0.69/0.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.69/0.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.69/0.92  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.69/0.92  thf(zf_stmt_5, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.69/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.69/0.92  thf('18', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.92         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.69/0.92          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.69/0.92          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.92  thf('19', plain,
% 0.69/0.92      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.69/0.92        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['17', '18'])).
% 0.69/0.92  thf('20', plain,
% 0.69/0.92      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.69/0.92        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['16', '19'])).
% 0.69/0.92  thf('21', plain,
% 0.69/0.92      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('22', plain,
% 0.69/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.92         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.69/0.92          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.69/0.92          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.69/0.92  thf('23', plain,
% 0.69/0.92      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.69/0.92        | ((u1_struct_0 @ sk_A)
% 0.69/0.92            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.92  thf('24', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_C @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(redefinition_k1_relset_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.69/0.92  thf('25', plain,
% 0.69/0.92      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.69/0.92         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.69/0.92          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.69/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.92  thf('26', plain,
% 0.69/0.92      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92         = (k1_relat_1 @ sk_C))),
% 0.69/0.92      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.92  thf('27', plain,
% 0.69/0.92      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.69/0.92        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['23', '26'])).
% 0.69/0.92  thf('28', plain,
% 0.69/0.92      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.69/0.92        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['20', '27'])).
% 0.69/0.92  thf('29', plain,
% 0.69/0.92      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.69/0.92        | ~ (l1_struct_0 @ sk_B)
% 0.69/0.92        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['15', '28'])).
% 0.69/0.92  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.69/0.92      inference('sup+', [status(thm)], ['2', '3'])).
% 0.69/0.92  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('32', plain,
% 0.69/0.92      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.69/0.92        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.69/0.92  thf('33', plain,
% 0.69/0.92      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.69/0.92        | ~ (l1_struct_0 @ sk_A)
% 0.69/0.92        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['14', '32'])).
% 0.69/0.92  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('35', plain,
% 0.69/0.92      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.69/0.92        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('demod', [status(thm)], ['33', '34'])).
% 0.69/0.92  thf('36', plain,
% 0.69/0.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.69/0.92          != (k2_struct_0 @ sk_B))
% 0.69/0.92        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.69/0.92            != (k2_struct_0 @ sk_A)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('37', plain,
% 0.69/0.92      (![X19 : $i]:
% 0.69/0.92         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.69/0.92  thf('38', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_C @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(d4_tops_2, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.92       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.69/0.92         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.69/0.92  thf('39', plain,
% 0.69/0.92      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.92         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.69/0.92          | ~ (v2_funct_1 @ X23)
% 0.69/0.92          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.69/0.92          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.69/0.92          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.69/0.92          | ~ (v1_funct_1 @ X23))),
% 0.69/0.92      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.69/0.92  thf('40', plain,
% 0.69/0.92      ((~ (v1_funct_1 @ sk_C)
% 0.69/0.92        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.69/0.92        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92            = (k2_funct_1 @ sk_C))
% 0.69/0.92        | ~ (v2_funct_1 @ sk_C)
% 0.69/0.92        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92            != (u1_struct_0 @ sk_B)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['38', '39'])).
% 0.69/0.92  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('42', plain,
% 0.69/0.92      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('43', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('44', plain,
% 0.69/0.92      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92         = (k2_relat_1 @ sk_C))),
% 0.69/0.92      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.92  thf('45', plain,
% 0.69/0.92      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92          = (k2_funct_1 @ sk_C))
% 0.69/0.92        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.69/0.92      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.69/0.92  thf('46', plain,
% 0.69/0.92      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.69/0.92        | ~ (l1_struct_0 @ sk_B)
% 0.69/0.92        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92            = (k2_funct_1 @ sk_C)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['37', '45'])).
% 0.69/0.92  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.69/0.92      inference('sup+', [status(thm)], ['2', '3'])).
% 0.69/0.92  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('49', plain,
% 0.69/0.92      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.69/0.92        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92            = (k2_funct_1 @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.69/0.92  thf('50', plain,
% 0.69/0.92      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92         = (k2_funct_1 @ sk_C))),
% 0.69/0.92      inference('simplify', [status(thm)], ['49'])).
% 0.69/0.92  thf('51', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.69/0.92      inference('sup+', [status(thm)], ['2', '3'])).
% 0.69/0.92  thf('52', plain,
% 0.69/0.92      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92         = (k2_funct_1 @ sk_C))),
% 0.69/0.92      inference('simplify', [status(thm)], ['49'])).
% 0.69/0.92  thf('53', plain,
% 0.69/0.92      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.69/0.92        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.69/0.92      inference('demod', [status(thm)], ['36', '50', '51', '52'])).
% 0.69/0.92  thf('54', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_C @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(dt_k2_tops_2, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.92       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.69/0.92         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.69/0.92         ( m1_subset_1 @
% 0.69/0.92           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.69/0.92           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.69/0.92  thf('55', plain,
% 0.69/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.69/0.92         ((m1_subset_1 @ (k2_tops_2 @ X24 @ X25 @ X26) @ 
% 0.69/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.69/0.92          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.69/0.92          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.69/0.92          | ~ (v1_funct_1 @ X26))),
% 0.69/0.92      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.69/0.92  thf('56', plain,
% 0.69/0.92      ((~ (v1_funct_1 @ sk_C)
% 0.69/0.92        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.69/0.92        | (m1_subset_1 @ 
% 0.69/0.92           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.69/0.92           (k1_zfmisc_1 @ 
% 0.69/0.92            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['54', '55'])).
% 0.69/0.92  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('58', plain,
% 0.69/0.92      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('59', plain,
% 0.69/0.92      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.69/0.92         = (k2_funct_1 @ sk_C))),
% 0.69/0.92      inference('simplify', [status(thm)], ['49'])).
% 0.69/0.92  thf('60', plain,
% 0.69/0.92      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.69/0.92      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.69/0.92  thf('61', plain,
% 0.69/0.92      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.69/0.92         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.69/0.92          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.69/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.92  thf('62', plain,
% 0.69/0.92      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['60', '61'])).
% 0.69/0.92  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(t55_funct_1, axiom,
% 0.69/0.92    (![A:$i]:
% 0.69/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.92       ( ( v2_funct_1 @ A ) =>
% 0.69/0.92         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.69/0.92           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.92  thf('64', plain,
% 0.69/0.92      (![X4 : $i]:
% 0.69/0.92         (~ (v2_funct_1 @ X4)
% 0.69/0.92          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.69/0.92          | ~ (v1_funct_1 @ X4)
% 0.69/0.92          | ~ (v1_relat_1 @ X4))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.69/0.92  thf('65', plain,
% 0.69/0.92      ((~ (v1_relat_1 @ sk_C)
% 0.69/0.92        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.69/0.92        | ~ (v2_funct_1 @ sk_C))),
% 0.69/0.92      inference('sup-', [status(thm)], ['63', '64'])).
% 0.69/0.92  thf('66', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_C @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(cc2_relat_1, axiom,
% 0.69/0.92    (![A:$i]:
% 0.69/0.92     ( ( v1_relat_1 @ A ) =>
% 0.69/0.92       ( ![B:$i]:
% 0.69/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.69/0.92  thf('67', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.92          | (v1_relat_1 @ X0)
% 0.69/0.92          | ~ (v1_relat_1 @ X1))),
% 0.69/0.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.92  thf('68', plain,
% 0.69/0.92      ((~ (v1_relat_1 @ 
% 0.69/0.92           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.69/0.92        | (v1_relat_1 @ sk_C))),
% 0.69/0.92      inference('sup-', [status(thm)], ['66', '67'])).
% 0.69/0.92  thf(fc6_relat_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.92  thf('69', plain,
% 0.69/0.92      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.69/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.92  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.92      inference('demod', [status(thm)], ['68', '69'])).
% 0.69/0.92  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('72', plain,
% 0.69/0.92      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['65', '70', '71'])).
% 0.69/0.92  thf('73', plain,
% 0.69/0.92      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.69/0.92      inference('demod', [status(thm)], ['62', '72'])).
% 0.69/0.92  thf('74', plain,
% 0.69/0.92      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.69/0.92        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.69/0.92      inference('demod', [status(thm)], ['53', '73'])).
% 0.69/0.92  thf('75', plain,
% 0.69/0.92      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.69/0.92      inference('simplify', [status(thm)], ['74'])).
% 0.69/0.92  thf('76', plain,
% 0.69/0.92      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.69/0.92        (k1_zfmisc_1 @ 
% 0.69/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.69/0.92      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.69/0.92  thf('77', plain,
% 0.69/0.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.92         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.69/0.92          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.69/0.92      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.92  thf('78', plain,
% 0.69/0.92      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['76', '77'])).
% 0.69/0.92  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('80', plain,
% 0.69/0.92      (![X4 : $i]:
% 0.69/0.92         (~ (v2_funct_1 @ X4)
% 0.69/0.92          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.69/0.92          | ~ (v1_funct_1 @ X4)
% 0.69/0.92          | ~ (v1_relat_1 @ X4))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.69/0.92  thf('81', plain,
% 0.69/0.92      ((~ (v1_relat_1 @ sk_C)
% 0.69/0.92        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.69/0.92        | ~ (v2_funct_1 @ sk_C))),
% 0.69/0.92      inference('sup-', [status(thm)], ['79', '80'])).
% 0.69/0.92  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.92      inference('demod', [status(thm)], ['68', '69'])).
% 0.69/0.92  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('84', plain,
% 0.69/0.92      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.69/0.92  thf('85', plain,
% 0.69/0.92      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.92         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.69/0.92      inference('demod', [status(thm)], ['78', '84'])).
% 0.69/0.92  thf('86', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.69/0.92      inference('demod', [status(thm)], ['75', '85'])).
% 0.69/0.92  thf('87', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['35', '86'])).
% 0.69/0.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.92  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.92  thf('89', plain, ($false),
% 0.69/0.92      inference('demod', [status(thm)], ['13', '87', '88'])).
% 0.69/0.92  
% 0.69/0.92  % SZS output end Refutation
% 0.69/0.92  
% 0.69/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
