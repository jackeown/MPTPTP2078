%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.11nwSwigTd

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:03 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 610 expanded)
%              Number of leaves         :   41 ( 193 expanded)
%              Depth                    :   17
%              Number of atoms          : 2132 (16294 expanded)
%              Number of equality atoms :  164 ( 915 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
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

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('37',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('74',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','50','61','62','74'])).

thf('76',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('93',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','93'])).

thf('95',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

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

thf('102',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('119',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104','111','119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','124'])).

thf('126',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('129',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('130',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','131','132','133'])).

thf('135',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('137',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('143',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('147',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['80'])).

thf('148',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('157',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','157'])).

thf('159',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('160',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('161',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','161'])).

thf('163',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['129','130'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['80'])).

thf('170',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['168','169'])).

thf('171',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['134','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','171'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('173',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('174',plain,(
    $false ),
    inference(demod,[status(thm)],['13','172','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.11nwSwigTd
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.08  % Solved by: fo/fo7.sh
% 0.89/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.08  % done 275 iterations in 0.612s
% 0.89/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.08  % SZS output start Refutation
% 0.89/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.08  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.89/1.08  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.89/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.89/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.08  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.89/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.89/1.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.89/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.08  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.89/1.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.89/1.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.08  thf(t62_tops_2, conjecture,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( l1_struct_0 @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.89/1.08           ( ![C:$i]:
% 0.89/1.08             ( ( ( v1_funct_1 @ C ) & 
% 0.89/1.08                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.08                 ( m1_subset_1 @
% 0.89/1.08                   C @ 
% 0.89/1.08                   ( k1_zfmisc_1 @
% 0.89/1.08                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.08               ( ( ( ( k2_relset_1 @
% 0.89/1.08                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.89/1.08                     ( k2_struct_0 @ B ) ) & 
% 0.89/1.08                   ( v2_funct_1 @ C ) ) =>
% 0.89/1.08                 ( ( ( k1_relset_1 @
% 0.89/1.08                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.08                       ( k2_tops_2 @
% 0.89/1.08                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.08                     ( k2_struct_0 @ B ) ) & 
% 0.89/1.08                   ( ( k2_relset_1 @
% 0.89/1.08                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.08                       ( k2_tops_2 @
% 0.89/1.08                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.08                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.08    (~( ![A:$i]:
% 0.89/1.08        ( ( l1_struct_0 @ A ) =>
% 0.89/1.08          ( ![B:$i]:
% 0.89/1.08            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.89/1.08              ( ![C:$i]:
% 0.89/1.08                ( ( ( v1_funct_1 @ C ) & 
% 0.89/1.08                    ( v1_funct_2 @
% 0.89/1.08                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.08                    ( m1_subset_1 @
% 0.89/1.08                      C @ 
% 0.89/1.08                      ( k1_zfmisc_1 @
% 0.89/1.08                        ( k2_zfmisc_1 @
% 0.89/1.08                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.08                  ( ( ( ( k2_relset_1 @
% 0.89/1.08                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.89/1.08                        ( k2_struct_0 @ B ) ) & 
% 0.89/1.08                      ( v2_funct_1 @ C ) ) =>
% 0.89/1.08                    ( ( ( k1_relset_1 @
% 0.89/1.08                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.08                          ( k2_tops_2 @
% 0.89/1.08                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.08                        ( k2_struct_0 @ B ) ) & 
% 0.89/1.08                      ( ( k2_relset_1 @
% 0.89/1.08                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.08                          ( k2_tops_2 @
% 0.89/1.08                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.89/1.08                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.89/1.08    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.89/1.08  thf('0', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(redefinition_k2_relset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.89/1.08  thf('1', plain,
% 0.89/1.08      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.89/1.08         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.89/1.08          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.08  thf('2', plain,
% 0.89/1.08      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k2_relat_1 @ sk_C))),
% 0.89/1.08      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.08  thf('3', plain,
% 0.89/1.08      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf(d3_struct_0, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.89/1.08  thf('5', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf(fc2_struct_0, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.89/1.08       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.89/1.08  thf('6', plain,
% 0.89/1.08      (![X23 : $i]:
% 0.89/1.08         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.89/1.08          | ~ (l1_struct_0 @ X23)
% 0.89/1.08          | (v2_struct_0 @ X23))),
% 0.89/1.08      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.89/1.08  thf('7', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | (v2_struct_0 @ X0)
% 0.89/1.08          | ~ (l1_struct_0 @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.08  thf('8', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v2_struct_0 @ X0)
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.89/1.08      inference('simplify', [status(thm)], ['7'])).
% 0.89/1.08  thf('9', plain,
% 0.89/1.08      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B)
% 0.89/1.08        | (v2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup-', [status(thm)], ['4', '8'])).
% 0.89/1.08  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('11', plain,
% 0.89/1.08      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.08  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.89/1.08      inference('clc', [status(thm)], ['11', '12'])).
% 0.89/1.08  thf('14', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('15', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf(d1_funct_2, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.89/1.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.89/1.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.89/1.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_1, axiom,
% 0.89/1.08    (![B:$i,A:$i]:
% 0.89/1.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.08       ( zip_tseitin_0 @ B @ A ) ))).
% 0.89/1.08  thf('16', plain,
% 0.89/1.08      (![X11 : $i, X12 : $i]:
% 0.89/1.08         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.08  thf('17', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.89/1.08  thf(zf_stmt_3, axiom,
% 0.89/1.08    (![C:$i,B:$i,A:$i]:
% 0.89/1.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.89/1.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.08  thf(zf_stmt_5, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.89/1.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.89/1.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.89/1.08  thf('18', plain,
% 0.89/1.08      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.08         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.89/1.08          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.89/1.08          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.08  thf('19', plain,
% 0.89/1.08      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.08        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.89/1.08  thf('20', plain,
% 0.89/1.08      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.89/1.08        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['16', '19'])).
% 0.89/1.08  thf('21', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('22', plain,
% 0.89/1.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.89/1.08         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.89/1.08          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.89/1.08          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.08  thf('23', plain,
% 0.89/1.08      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.08        | ((u1_struct_0 @ sk_A)
% 0.89/1.08            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['21', '22'])).
% 0.89/1.08  thf('24', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(redefinition_k1_relset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.89/1.08  thf('25', plain,
% 0.89/1.08      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.89/1.08         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.89/1.08          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.08  thf('26', plain,
% 0.89/1.08      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k1_relat_1 @ sk_C))),
% 0.89/1.08      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.08  thf('27', plain,
% 0.89/1.08      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.08        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.89/1.08      inference('demod', [status(thm)], ['23', '26'])).
% 0.89/1.08  thf('28', plain,
% 0.89/1.08      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.89/1.08        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['20', '27'])).
% 0.89/1.08  thf('29', plain,
% 0.89/1.08      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B)
% 0.89/1.08        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['15', '28'])).
% 0.89/1.08  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('32', plain,
% 0.89/1.08      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.89/1.08        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.89/1.08      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.89/1.08  thf('33', plain,
% 0.89/1.08      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_A)
% 0.89/1.08        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['14', '32'])).
% 0.89/1.08  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('35', plain,
% 0.89/1.08      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.89/1.08        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.89/1.08      inference('demod', [status(thm)], ['33', '34'])).
% 0.89/1.08  thf(t55_funct_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.08       ( ( v2_funct_1 @ A ) =>
% 0.89/1.08         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.89/1.08           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.89/1.08  thf('36', plain,
% 0.89/1.08      (![X4 : $i]:
% 0.89/1.08         (~ (v2_funct_1 @ X4)
% 0.89/1.08          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.89/1.08          | ~ (v1_funct_1 @ X4)
% 0.89/1.08          | ~ (v1_relat_1 @ X4))),
% 0.89/1.08      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.08  thf('37', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('38', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('39', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('40', plain,
% 0.89/1.08      (((m1_subset_1 @ sk_C @ 
% 0.89/1.08         (k1_zfmisc_1 @ 
% 0.89/1.08          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.08      inference('sup+', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('42', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.08      inference('demod', [status(thm)], ['40', '41'])).
% 0.89/1.08  thf('43', plain,
% 0.89/1.08      (((m1_subset_1 @ sk_C @ 
% 0.89/1.08         (k1_zfmisc_1 @ 
% 0.89/1.08          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['37', '42'])).
% 0.89/1.08  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('45', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.89/1.08      inference('demod', [status(thm)], ['43', '44'])).
% 0.89/1.08  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('47', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.08      inference('demod', [status(thm)], ['45', '46'])).
% 0.89/1.08  thf(d4_tops_2, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.89/1.08         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.89/1.08  thf('48', plain,
% 0.89/1.08      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.89/1.08         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 0.89/1.08          | ~ (v2_funct_1 @ X26)
% 0.89/1.08          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 0.89/1.08          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.89/1.08          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 0.89/1.08          | ~ (v1_funct_1 @ X26))),
% 0.89/1.08      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.89/1.08  thf('49', plain,
% 0.89/1.08      ((~ (v1_funct_1 @ sk_C)
% 0.89/1.08        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.89/1.08        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.08            = (k2_funct_1 @ sk_C))
% 0.89/1.08        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.08        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.08            != (k2_relat_1 @ sk_C)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.08  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('51', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('52', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('53', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('54', plain,
% 0.89/1.08      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.08      inference('sup+', [status(thm)], ['52', '53'])).
% 0.89/1.08  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('56', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['54', '55'])).
% 0.89/1.08  thf('57', plain,
% 0.89/1.08      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['51', '56'])).
% 0.89/1.08  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('59', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['57', '58'])).
% 0.89/1.08  thf('60', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('61', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.89/1.08      inference('demod', [status(thm)], ['59', '60'])).
% 0.89/1.08  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('63', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('64', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('65', plain,
% 0.89/1.08      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('66', plain,
% 0.89/1.08      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08          = (k2_struct_0 @ sk_B))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.08      inference('sup+', [status(thm)], ['64', '65'])).
% 0.89/1.08  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('68', plain,
% 0.89/1.08      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['66', '67'])).
% 0.89/1.08  thf('69', plain,
% 0.89/1.08      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08          = (k2_struct_0 @ sk_B))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['63', '68'])).
% 0.89/1.08  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('71', plain,
% 0.89/1.08      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['69', '70'])).
% 0.89/1.08  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('74', plain,
% 0.89/1.08      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.08         = (k2_relat_1 @ sk_C))),
% 0.89/1.08      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.89/1.08  thf('75', plain,
% 0.89/1.08      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.08          = (k2_funct_1 @ sk_C))
% 0.89/1.08        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.89/1.08      inference('demod', [status(thm)], ['49', '50', '61', '62', '74'])).
% 0.89/1.08  thf('76', plain,
% 0.89/1.08      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.08         = (k2_funct_1 @ sk_C))),
% 0.89/1.08      inference('simplify', [status(thm)], ['75'])).
% 0.89/1.08  thf('77', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('78', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('79', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('80', plain,
% 0.89/1.08      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08          != (k2_struct_0 @ sk_B))
% 0.89/1.08        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08            != (k2_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('81', plain,
% 0.89/1.08      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08          != (k2_struct_0 @ sk_A)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('split', [status(esa)], ['80'])).
% 0.89/1.08  thf('82', plain,
% 0.89/1.08      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08           != (k2_struct_0 @ sk_A))
% 0.89/1.08         | ~ (l1_struct_0 @ sk_B)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['79', '81'])).
% 0.89/1.08  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('84', plain,
% 0.89/1.08      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08          != (k2_struct_0 @ sk_A)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('demod', [status(thm)], ['82', '83'])).
% 0.89/1.08  thf('85', plain,
% 0.89/1.08      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08           != (k2_struct_0 @ sk_A))
% 0.89/1.08         | ~ (l1_struct_0 @ sk_A)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['78', '84'])).
% 0.89/1.08  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('87', plain,
% 0.89/1.08      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08          != (k2_struct_0 @ sk_A)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('demod', [status(thm)], ['85', '86'])).
% 0.89/1.08  thf('88', plain,
% 0.89/1.08      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08           != (k2_struct_0 @ sk_A))
% 0.89/1.08         | ~ (l1_struct_0 @ sk_B)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['77', '87'])).
% 0.89/1.08  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('90', plain,
% 0.89/1.08      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08          != (k2_struct_0 @ sk_A)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('demod', [status(thm)], ['88', '89'])).
% 0.89/1.08  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('93', plain,
% 0.89/1.08      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.08          != (k2_struct_0 @ sk_A)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.89/1.08  thf('94', plain,
% 0.89/1.08      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.08                = (k2_struct_0 @ sk_A))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['76', '93'])).
% 0.89/1.08  thf('95', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('96', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('97', plain,
% 0.89/1.08      (((m1_subset_1 @ sk_C @ 
% 0.89/1.08         (k1_zfmisc_1 @ 
% 0.89/1.08          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['95', '96'])).
% 0.89/1.08  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('99', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.89/1.08      inference('demod', [status(thm)], ['97', '98'])).
% 0.89/1.08  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('101', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_C @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.08      inference('demod', [status(thm)], ['99', '100'])).
% 0.89/1.08  thf(t31_funct_2, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.89/1.08         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.89/1.08           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.89/1.08           ( m1_subset_1 @
% 0.89/1.08             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.89/1.08  thf('102', plain,
% 0.89/1.08      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.89/1.08         (~ (v2_funct_1 @ X19)
% 0.89/1.08          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 0.89/1.08          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 0.89/1.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.89/1.08          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.89/1.08          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 0.89/1.08          | ~ (v1_funct_1 @ X19))),
% 0.89/1.08      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.89/1.08  thf('103', plain,
% 0.89/1.08      ((~ (v1_funct_1 @ sk_C)
% 0.89/1.08        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.89/1.08        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.08           (k1_zfmisc_1 @ 
% 0.89/1.08            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.08            != (k2_relat_1 @ sk_C))
% 0.89/1.08        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.08      inference('sup-', [status(thm)], ['101', '102'])).
% 0.89/1.08  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('105', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('106', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('107', plain,
% 0.89/1.08      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['105', '106'])).
% 0.89/1.08  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('109', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['107', '108'])).
% 0.89/1.08  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('111', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.89/1.08      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.08  thf('112', plain,
% 0.89/1.08      (![X22 : $i]:
% 0.89/1.08         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.08  thf('113', plain,
% 0.89/1.08      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('114', plain,
% 0.89/1.08      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08          = (k2_struct_0 @ sk_B))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['112', '113'])).
% 0.89/1.08  thf('115', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('116', plain,
% 0.89/1.08      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.89/1.08         = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['114', '115'])).
% 0.89/1.08  thf('117', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.08  thf('119', plain,
% 0.89/1.08      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.08         = (k2_relat_1 @ sk_C))),
% 0.89/1.08      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.89/1.08  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('121', plain,
% 0.89/1.08      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.08         (k1_zfmisc_1 @ 
% 0.89/1.08          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.89/1.08      inference('demod', [status(thm)], ['103', '104', '111', '119', '120'])).
% 0.89/1.08  thf('122', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.09        (k1_zfmisc_1 @ 
% 0.89/1.09         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.09      inference('simplify', [status(thm)], ['121'])).
% 0.89/1.09  thf('123', plain,
% 0.89/1.09      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.89/1.09         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.89/1.09          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.89/1.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.09  thf('124', plain,
% 0.89/1.09      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['122', '123'])).
% 0.89/1.09  thf('125', plain,
% 0.89/1.09      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('demod', [status(thm)], ['94', '124'])).
% 0.89/1.09  thf('126', plain,
% 0.89/1.09      (((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.89/1.09         | ~ (v1_relat_1 @ sk_C)
% 0.89/1.09         | ~ (v1_funct_1 @ sk_C)
% 0.89/1.09         | ~ (v2_funct_1 @ sk_C)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['36', '125'])).
% 0.89/1.09  thf('127', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_C @ 
% 0.89/1.09        (k1_zfmisc_1 @ 
% 0.89/1.09         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(cc2_relat_1, axiom,
% 0.89/1.09    (![A:$i]:
% 0.89/1.09     ( ( v1_relat_1 @ A ) =>
% 0.89/1.09       ( ![B:$i]:
% 0.89/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.89/1.09  thf('128', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.89/1.09          | (v1_relat_1 @ X0)
% 0.89/1.09          | ~ (v1_relat_1 @ X1))),
% 0.89/1.09      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.09  thf('129', plain,
% 0.89/1.09      ((~ (v1_relat_1 @ 
% 0.89/1.09           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.89/1.09        | (v1_relat_1 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['127', '128'])).
% 0.89/1.09  thf(fc6_relat_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.09  thf('130', plain,
% 0.89/1.09      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.09  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.09      inference('demod', [status(thm)], ['129', '130'])).
% 0.89/1.09  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('134', plain,
% 0.89/1.09      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_A))))),
% 0.89/1.09      inference('demod', [status(thm)], ['126', '131', '132', '133'])).
% 0.89/1.09  thf('135', plain,
% 0.89/1.09      (![X4 : $i]:
% 0.89/1.09         (~ (v2_funct_1 @ X4)
% 0.89/1.09          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.89/1.09          | ~ (v1_funct_1 @ X4)
% 0.89/1.09          | ~ (v1_relat_1 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.89/1.09  thf('136', plain,
% 0.89/1.09      ((m1_subset_1 @ sk_C @ 
% 0.89/1.09        (k1_zfmisc_1 @ 
% 0.89/1.09         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.89/1.09      inference('demod', [status(thm)], ['99', '100'])).
% 0.89/1.09  thf('137', plain,
% 0.89/1.09      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.89/1.09         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 0.89/1.09          | ~ (v2_funct_1 @ X26)
% 0.89/1.09          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 0.89/1.09          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.89/1.09          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 0.89/1.09          | ~ (v1_funct_1 @ X26))),
% 0.89/1.09      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.89/1.09  thf('138', plain,
% 0.89/1.09      ((~ (v1_funct_1 @ sk_C)
% 0.89/1.09        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.89/1.09        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.09            = (k2_funct_1 @ sk_C))
% 0.89/1.09        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.09        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.09            != (k2_relat_1 @ sk_C)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['136', '137'])).
% 0.89/1.09  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('140', plain,
% 0.89/1.09      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.89/1.09      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.09  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('142', plain,
% 0.89/1.09      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.09         = (k2_relat_1 @ sk_C))),
% 0.89/1.09      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.89/1.09  thf('143', plain,
% 0.89/1.09      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.09          = (k2_funct_1 @ sk_C))
% 0.89/1.09        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.89/1.09      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 0.89/1.09  thf('144', plain,
% 0.89/1.09      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.89/1.09         = (k2_funct_1 @ sk_C))),
% 0.89/1.09      inference('simplify', [status(thm)], ['143'])).
% 0.89/1.09  thf('145', plain,
% 0.89/1.09      (![X22 : $i]:
% 0.89/1.09         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.09  thf('146', plain,
% 0.89/1.09      (![X22 : $i]:
% 0.89/1.09         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.89/1.09  thf('147', plain,
% 0.89/1.09      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09          != (k2_struct_0 @ sk_B)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('split', [status(esa)], ['80'])).
% 0.89/1.09  thf('148', plain,
% 0.89/1.09      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09           != (k2_struct_0 @ sk_B))
% 0.89/1.09         | ~ (l1_struct_0 @ sk_B)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['146', '147'])).
% 0.89/1.09  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('150', plain,
% 0.89/1.09      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09          != (k2_struct_0 @ sk_B)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('demod', [status(thm)], ['148', '149'])).
% 0.89/1.09  thf('151', plain,
% 0.89/1.09      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09           != (k2_struct_0 @ sk_B))
% 0.89/1.09         | ~ (l1_struct_0 @ sk_B)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['145', '150'])).
% 0.89/1.09  thf('152', plain, ((l1_struct_0 @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('153', plain,
% 0.89/1.09      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09          != (k2_struct_0 @ sk_B)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('demod', [status(thm)], ['151', '152'])).
% 0.89/1.09  thf('154', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.09      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.09  thf('155', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.09      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.09  thf('156', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.89/1.09      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.09  thf('157', plain,
% 0.89/1.09      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.89/1.09          != (k2_relat_1 @ sk_C)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 0.89/1.09  thf('158', plain,
% 0.89/1.09      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['144', '157'])).
% 0.89/1.09  thf('159', plain,
% 0.89/1.09      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.89/1.09        (k1_zfmisc_1 @ 
% 0.89/1.09         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.09      inference('simplify', [status(thm)], ['121'])).
% 0.89/1.09  thf('160', plain,
% 0.89/1.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.89/1.09         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.89/1.09          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.89/1.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.09  thf('161', plain,
% 0.89/1.09      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['159', '160'])).
% 0.89/1.09  thf('162', plain,
% 0.89/1.09      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('demod', [status(thm)], ['158', '161'])).
% 0.89/1.09  thf('163', plain,
% 0.89/1.09      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.89/1.09         | ~ (v1_relat_1 @ sk_C)
% 0.89/1.09         | ~ (v1_funct_1 @ sk_C)
% 0.89/1.09         | ~ (v2_funct_1 @ sk_C)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['135', '162'])).
% 0.89/1.09  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.09      inference('demod', [status(thm)], ['129', '130'])).
% 0.89/1.09  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('167', plain,
% 0.89/1.09      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.89/1.09         <= (~
% 0.89/1.09             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09                = (k2_struct_0 @ sk_B))))),
% 0.89/1.09      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 0.89/1.09  thf('168', plain,
% 0.89/1.09      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09          = (k2_struct_0 @ sk_B)))),
% 0.89/1.09      inference('simplify', [status(thm)], ['167'])).
% 0.89/1.09  thf('169', plain,
% 0.89/1.09      (~
% 0.89/1.09       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09          = (k2_struct_0 @ sk_A))) | 
% 0.89/1.09       ~
% 0.89/1.09       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09          = (k2_struct_0 @ sk_B)))),
% 0.89/1.09      inference('split', [status(esa)], ['80'])).
% 0.89/1.09  thf('170', plain,
% 0.89/1.09      (~
% 0.89/1.09       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.09          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.89/1.09          = (k2_struct_0 @ sk_A)))),
% 0.89/1.09      inference('sat_resolution*', [status(thm)], ['168', '169'])).
% 0.89/1.09  thf('171', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.89/1.09      inference('simpl_trail', [status(thm)], ['134', '170'])).
% 0.89/1.09  thf('172', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['35', '171'])).
% 0.89/1.09  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.89/1.09  thf('173', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.09  thf('174', plain, ($false),
% 0.89/1.09      inference('demod', [status(thm)], ['13', '172', '173'])).
% 0.89/1.09  
% 0.89/1.09  % SZS output end Refutation
% 0.89/1.09  
% 0.89/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
