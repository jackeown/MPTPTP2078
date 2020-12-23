%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1wMcTPGWH

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:55 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 613 expanded)
%              Number of leaves         :   40 ( 194 expanded)
%              Depth                    :   18
%              Number of atoms          : 1726 (16614 expanded)
%              Number of equality atoms :  136 ( 926 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 )
      | ( X10 = k1_xboole_0 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X16 )
      | ( zip_tseitin_1 @ X17 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ( X12
        = ( k1_relset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X12 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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

thf('36',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('43',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ X22 )
       != X20 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_tops_2 @ X21 @ X20 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('51',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X23 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('75',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ X22 )
       != X20 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_tops_2 @ X21 @ X20 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','87'])).

thf('89',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','73','89'])).

thf('91',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('92',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
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

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('99',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','101'])).

thf('103',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','56','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('105',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','73','89'])).

thf('106',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('107',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('109',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['37'])).

thf('112',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('121',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','121'])).

thf('123',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','122'])).

thf('124',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['37'])).

thf('131',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['129','130'])).

thf('132',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['103','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','132'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['13','133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1wMcTPGWH
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.86/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.86/1.04  % Solved by: fo/fo7.sh
% 0.86/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.04  % done 371 iterations in 0.558s
% 0.86/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.86/1.04  % SZS output start Refutation
% 0.86/1.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.86/1.04  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.86/1.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.86/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.86/1.04  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.86/1.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.86/1.04  thf(sk_C_type, type, sk_C: $i).
% 0.86/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.86/1.04  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.86/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.86/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.86/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.86/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.86/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.86/1.04  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.86/1.04  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.86/1.04  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.86/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.86/1.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.86/1.04  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.86/1.04  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.86/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.86/1.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.86/1.04  thf(t62_tops_2, conjecture,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( l1_struct_0 @ A ) =>
% 0.86/1.04       ( ![B:$i]:
% 0.86/1.04         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.86/1.04           ( ![C:$i]:
% 0.86/1.04             ( ( ( v1_funct_1 @ C ) & 
% 0.86/1.04                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.86/1.04                 ( m1_subset_1 @
% 0.86/1.04                   C @ 
% 0.86/1.04                   ( k1_zfmisc_1 @
% 0.86/1.04                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.86/1.04               ( ( ( ( k2_relset_1 @
% 0.86/1.04                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.86/1.04                     ( k2_struct_0 @ B ) ) & 
% 0.86/1.04                   ( v2_funct_1 @ C ) ) =>
% 0.86/1.04                 ( ( ( k1_relset_1 @
% 0.86/1.04                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04                       ( k2_tops_2 @
% 0.86/1.04                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.86/1.04                     ( k2_struct_0 @ B ) ) & 
% 0.86/1.04                   ( ( k2_relset_1 @
% 0.86/1.04                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04                       ( k2_tops_2 @
% 0.86/1.04                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.86/1.04                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.86/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.04    (~( ![A:$i]:
% 0.86/1.04        ( ( l1_struct_0 @ A ) =>
% 0.86/1.04          ( ![B:$i]:
% 0.86/1.04            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.86/1.04              ( ![C:$i]:
% 0.86/1.04                ( ( ( v1_funct_1 @ C ) & 
% 0.86/1.04                    ( v1_funct_2 @
% 0.86/1.04                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.86/1.04                    ( m1_subset_1 @
% 0.86/1.04                      C @ 
% 0.86/1.04                      ( k1_zfmisc_1 @
% 0.86/1.04                        ( k2_zfmisc_1 @
% 0.86/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.86/1.04                  ( ( ( ( k2_relset_1 @
% 0.86/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.86/1.04                        ( k2_struct_0 @ B ) ) & 
% 0.86/1.04                      ( v2_funct_1 @ C ) ) =>
% 0.86/1.04                    ( ( ( k1_relset_1 @
% 0.86/1.04                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04                          ( k2_tops_2 @
% 0.86/1.04                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.86/1.04                        ( k2_struct_0 @ B ) ) & 
% 0.86/1.04                      ( ( k2_relset_1 @
% 0.86/1.04                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04                          ( k2_tops_2 @
% 0.86/1.04                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.86/1.04                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.86/1.04    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.86/1.04  thf('0', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(redefinition_k2_relset_1, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.86/1.04  thf('1', plain,
% 0.86/1.04      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.86/1.04         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.86/1.04          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.86/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.86/1.04  thf('2', plain,
% 0.86/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04         = (k2_relat_1 @ sk_C))),
% 0.86/1.04      inference('sup-', [status(thm)], ['0', '1'])).
% 0.86/1.04  thf('3', plain,
% 0.86/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04         = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf(d3_struct_0, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.86/1.04  thf('5', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf(fc2_struct_0, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.86/1.04       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.86/1.04  thf('6', plain,
% 0.86/1.04      (![X19 : $i]:
% 0.86/1.04         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.86/1.04          | ~ (l1_struct_0 @ X19)
% 0.86/1.04          | (v2_struct_0 @ X19))),
% 0.86/1.04      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.86/1.04  thf('7', plain,
% 0.86/1.04      (![X0 : $i]:
% 0.86/1.04         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.86/1.04          | ~ (l1_struct_0 @ X0)
% 0.86/1.04          | (v2_struct_0 @ X0)
% 0.86/1.04          | ~ (l1_struct_0 @ X0))),
% 0.86/1.04      inference('sup-', [status(thm)], ['5', '6'])).
% 0.86/1.04  thf('8', plain,
% 0.86/1.04      (![X0 : $i]:
% 0.86/1.04         ((v2_struct_0 @ X0)
% 0.86/1.04          | ~ (l1_struct_0 @ X0)
% 0.86/1.04          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.86/1.04      inference('simplify', [status(thm)], ['7'])).
% 0.86/1.04  thf('9', plain,
% 0.86/1.04      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.86/1.04        | ~ (l1_struct_0 @ sk_B)
% 0.86/1.04        | (v2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup-', [status(thm)], ['4', '8'])).
% 0.86/1.04  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('11', plain,
% 0.86/1.04      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.86/1.04      inference('demod', [status(thm)], ['9', '10'])).
% 0.86/1.04  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.86/1.04      inference('clc', [status(thm)], ['11', '12'])).
% 0.86/1.04  thf('14', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('15', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf(d1_funct_2, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.04       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.86/1.04           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.86/1.04             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.86/1.04         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.86/1.04           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.86/1.04             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.86/1.04  thf(zf_stmt_1, axiom,
% 0.86/1.04    (![B:$i,A:$i]:
% 0.86/1.04     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.86/1.04       ( zip_tseitin_0 @ B @ A ) ))).
% 0.86/1.04  thf('16', plain,
% 0.86/1.04      (![X10 : $i, X11 : $i]:
% 0.86/1.04         ((zip_tseitin_0 @ X10 @ X11) | ((X10) = (k1_xboole_0)))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.86/1.04  thf('17', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.86/1.04  thf(zf_stmt_3, axiom,
% 0.86/1.04    (![C:$i,B:$i,A:$i]:
% 0.86/1.04     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.86/1.04       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.86/1.04  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.86/1.04  thf(zf_stmt_5, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.04       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.86/1.04         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.86/1.04           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.86/1.04             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.86/1.04  thf('18', plain,
% 0.86/1.04      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.86/1.04         (~ (zip_tseitin_0 @ X15 @ X16)
% 0.86/1.04          | (zip_tseitin_1 @ X17 @ X15 @ X16)
% 0.86/1.04          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15))))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.04  thf('19', plain,
% 0.86/1.04      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.86/1.04        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['17', '18'])).
% 0.86/1.04  thf('20', plain,
% 0.86/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.86/1.04        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['16', '19'])).
% 0.86/1.04  thf('21', plain,
% 0.86/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('22', plain,
% 0.86/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.86/1.04         (~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.86/1.04          | ((X12) = (k1_relset_1 @ X12 @ X13 @ X14))
% 0.86/1.04          | ~ (zip_tseitin_1 @ X14 @ X13 @ X12))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.86/1.04  thf('23', plain,
% 0.86/1.04      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.86/1.04        | ((u1_struct_0 @ sk_A)
% 0.86/1.04            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['21', '22'])).
% 0.86/1.04  thf('24', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(redefinition_k1_relset_1, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.04       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.86/1.04  thf('25', plain,
% 0.86/1.04      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.86/1.04         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.86/1.04          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.86/1.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.86/1.04  thf('26', plain,
% 0.86/1.04      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04         = (k1_relat_1 @ sk_C))),
% 0.86/1.04      inference('sup-', [status(thm)], ['24', '25'])).
% 0.86/1.04  thf('27', plain,
% 0.86/1.04      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.86/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.86/1.04      inference('demod', [status(thm)], ['23', '26'])).
% 0.86/1.04  thf('28', plain,
% 0.86/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.86/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['20', '27'])).
% 0.86/1.04  thf('29', plain,
% 0.86/1.04      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.86/1.04        | ~ (l1_struct_0 @ sk_B)
% 0.86/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.86/1.04      inference('sup+', [status(thm)], ['15', '28'])).
% 0.86/1.04  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('32', plain,
% 0.86/1.04      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.86/1.04        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.86/1.04      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.86/1.04  thf('33', plain,
% 0.86/1.04      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.86/1.04        | ~ (l1_struct_0 @ sk_A)
% 0.86/1.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.86/1.04      inference('sup+', [status(thm)], ['14', '32'])).
% 0.86/1.04  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('35', plain,
% 0.86/1.04      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.86/1.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.86/1.04      inference('demod', [status(thm)], ['33', '34'])).
% 0.86/1.04  thf('36', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('37', plain,
% 0.86/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          != (k2_struct_0 @ sk_B))
% 0.86/1.04        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04            != (k2_struct_0 @ sk_A)))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('38', plain,
% 0.86/1.04      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          != (k2_struct_0 @ sk_A)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_A))))),
% 0.86/1.04      inference('split', [status(esa)], ['37'])).
% 0.86/1.04  thf('39', plain,
% 0.86/1.04      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04           != (k2_struct_0 @ sk_A))
% 0.86/1.04         | ~ (l1_struct_0 @ sk_B)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_A))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['36', '38'])).
% 0.86/1.04  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('41', plain,
% 0.86/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          != (k2_struct_0 @ sk_A)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_A))))),
% 0.86/1.04      inference('demod', [status(thm)], ['39', '40'])).
% 0.86/1.04  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('43', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('44', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(d4_tops_2, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.86/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.86/1.04       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.86/1.04         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.86/1.04  thf('45', plain,
% 0.86/1.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.86/1.04         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.86/1.04          | ~ (v2_funct_1 @ X22)
% 0.86/1.04          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.86/1.04          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.86/1.04          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.86/1.04          | ~ (v1_funct_1 @ X22))),
% 0.86/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.86/1.04  thf('46', plain,
% 0.86/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.86/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.86/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04            = (k2_funct_1 @ sk_C))
% 0.86/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.86/1.04        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04            != (u1_struct_0 @ sk_B)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['44', '45'])).
% 0.86/1.04  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('48', plain,
% 0.86/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('50', plain,
% 0.86/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04         = (k2_relat_1 @ sk_C))),
% 0.86/1.04      inference('sup-', [status(thm)], ['0', '1'])).
% 0.86/1.04  thf('51', plain,
% 0.86/1.04      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04          = (k2_funct_1 @ sk_C))
% 0.86/1.04        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.86/1.04      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.86/1.04  thf('52', plain,
% 0.86/1.04      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.86/1.04        | ~ (l1_struct_0 @ sk_B)
% 0.86/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04            = (k2_funct_1 @ sk_C)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['43', '51'])).
% 0.86/1.04  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('55', plain,
% 0.86/1.04      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.86/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04            = (k2_funct_1 @ sk_C)))),
% 0.86/1.04      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.86/1.04  thf('56', plain,
% 0.86/1.04      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04         = (k2_funct_1 @ sk_C))),
% 0.86/1.04      inference('simplify', [status(thm)], ['55'])).
% 0.86/1.04  thf('57', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('58', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('59', plain,
% 0.86/1.04      (((m1_subset_1 @ sk_C @ 
% 0.86/1.04         (k1_zfmisc_1 @ 
% 0.86/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.86/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('61', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('demod', [status(thm)], ['59', '60'])).
% 0.86/1.04  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('63', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.86/1.04      inference('demod', [status(thm)], ['61', '62'])).
% 0.86/1.04  thf(dt_k2_tops_2, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.86/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.86/1.04       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.86/1.04         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.86/1.04         ( m1_subset_1 @
% 0.86/1.04           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.86/1.04           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.86/1.04  thf('64', plain,
% 0.86/1.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.86/1.04         ((m1_subset_1 @ (k2_tops_2 @ X23 @ X24 @ X25) @ 
% 0.86/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.86/1.04          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.86/1.04          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.86/1.04          | ~ (v1_funct_1 @ X25))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.86/1.04  thf('65', plain,
% 0.86/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.86/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.86/1.04        | (m1_subset_1 @ 
% 0.86/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.86/1.04           (k1_zfmisc_1 @ 
% 0.86/1.04            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['63', '64'])).
% 0.86/1.04  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('67', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('68', plain,
% 0.86/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('69', plain,
% 0.86/1.04      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.86/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['67', '68'])).
% 0.86/1.04  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('71', plain,
% 0.86/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('demod', [status(thm)], ['69', '70'])).
% 0.86/1.04  thf('72', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('73', plain,
% 0.86/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.86/1.04      inference('demod', [status(thm)], ['71', '72'])).
% 0.86/1.04  thf('74', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.86/1.04      inference('demod', [status(thm)], ['61', '62'])).
% 0.86/1.04  thf('75', plain,
% 0.86/1.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.86/1.04         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.86/1.04          | ~ (v2_funct_1 @ X22)
% 0.86/1.04          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.86/1.04          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.86/1.04          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.86/1.04          | ~ (v1_funct_1 @ X22))),
% 0.86/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.86/1.04  thf('76', plain,
% 0.86/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.86/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.86/1.04        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.86/1.04            = (k2_funct_1 @ sk_C))
% 0.86/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.86/1.04        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.86/1.04            != (k2_relat_1 @ sk_C)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['74', '75'])).
% 0.86/1.04  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('78', plain,
% 0.86/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.86/1.04      inference('demod', [status(thm)], ['71', '72'])).
% 0.86/1.04  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('80', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('81', plain,
% 0.86/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04         = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('82', plain,
% 0.86/1.04      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04          = (k2_struct_0 @ sk_B))
% 0.86/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['80', '81'])).
% 0.86/1.04  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('84', plain,
% 0.86/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.86/1.04         = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('demod', [status(thm)], ['82', '83'])).
% 0.86/1.04  thf('85', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('87', plain,
% 0.86/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.86/1.04         = (k2_relat_1 @ sk_C))),
% 0.86/1.04      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.86/1.04  thf('88', plain,
% 0.86/1.04      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.86/1.04          = (k2_funct_1 @ sk_C))
% 0.86/1.04        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.86/1.04      inference('demod', [status(thm)], ['76', '77', '78', '79', '87'])).
% 0.86/1.04  thf('89', plain,
% 0.86/1.04      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.86/1.04         = (k2_funct_1 @ sk_C))),
% 0.86/1.04      inference('simplify', [status(thm)], ['88'])).
% 0.86/1.04  thf('90', plain,
% 0.86/1.04      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.86/1.04      inference('demod', [status(thm)], ['65', '66', '73', '89'])).
% 0.86/1.04  thf('91', plain,
% 0.86/1.04      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.86/1.04         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.86/1.04          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.86/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.86/1.04  thf('92', plain,
% 0.86/1.04      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['90', '91'])).
% 0.86/1.04  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(t55_funct_1, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.86/1.04       ( ( v2_funct_1 @ A ) =>
% 0.86/1.04         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.86/1.04           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.86/1.04  thf('94', plain,
% 0.86/1.04      (![X0 : $i]:
% 0.86/1.04         (~ (v2_funct_1 @ X0)
% 0.86/1.04          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.04          | ~ (v1_funct_1 @ X0)
% 0.86/1.04          | ~ (v1_relat_1 @ X0))),
% 0.86/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.86/1.04  thf('95', plain,
% 0.86/1.04      ((~ (v1_relat_1 @ sk_C)
% 0.86/1.04        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.86/1.04        | ~ (v2_funct_1 @ sk_C))),
% 0.86/1.04      inference('sup-', [status(thm)], ['93', '94'])).
% 0.86/1.04  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('97', plain,
% 0.86/1.04      ((~ (v1_relat_1 @ sk_C)
% 0.86/1.04        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.86/1.04      inference('demod', [status(thm)], ['95', '96'])).
% 0.86/1.04  thf('98', plain,
% 0.86/1.04      ((m1_subset_1 @ sk_C @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(cc1_relset_1, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i]:
% 0.86/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.04       ( v1_relat_1 @ C ) ))).
% 0.86/1.04  thf('99', plain,
% 0.86/1.04      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.86/1.04         ((v1_relat_1 @ X1)
% 0.86/1.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.86/1.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.86/1.04  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 0.86/1.04      inference('sup-', [status(thm)], ['98', '99'])).
% 0.86/1.04  thf('101', plain,
% 0.86/1.04      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.86/1.04      inference('demod', [status(thm)], ['97', '100'])).
% 0.86/1.04  thf('102', plain,
% 0.86/1.04      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.86/1.04      inference('demod', [status(thm)], ['92', '101'])).
% 0.86/1.04  thf('103', plain,
% 0.86/1.04      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_A))))),
% 0.86/1.04      inference('demod', [status(thm)], ['41', '42', '56', '102'])).
% 0.86/1.04  thf('104', plain,
% 0.86/1.04      (![X0 : $i]:
% 0.86/1.04         (~ (v2_funct_1 @ X0)
% 0.86/1.04          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.04          | ~ (v1_funct_1 @ X0)
% 0.86/1.04          | ~ (v1_relat_1 @ X0))),
% 0.86/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.86/1.04  thf('105', plain,
% 0.86/1.04      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.86/1.04      inference('demod', [status(thm)], ['65', '66', '73', '89'])).
% 0.86/1.04  thf('106', plain,
% 0.86/1.04      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.86/1.04         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.86/1.04          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.86/1.04      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.86/1.04  thf('107', plain,
% 0.86/1.04      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['105', '106'])).
% 0.86/1.04  thf('108', plain,
% 0.86/1.04      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.86/1.04         = (k2_funct_1 @ sk_C))),
% 0.86/1.04      inference('simplify', [status(thm)], ['88'])).
% 0.86/1.04  thf('109', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('110', plain,
% 0.86/1.04      (![X18 : $i]:
% 0.86/1.04         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.86/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.86/1.04  thf('111', plain,
% 0.86/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          != (k2_struct_0 @ sk_B)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('split', [status(esa)], ['37'])).
% 0.86/1.04  thf('112', plain,
% 0.86/1.04      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04           != (k2_struct_0 @ sk_B))
% 0.86/1.04         | ~ (l1_struct_0 @ sk_B)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['110', '111'])).
% 0.86/1.04  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('114', plain,
% 0.86/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          != (k2_struct_0 @ sk_B)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('demod', [status(thm)], ['112', '113'])).
% 0.86/1.04  thf('115', plain,
% 0.86/1.04      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04           != (k2_struct_0 @ sk_B))
% 0.86/1.04         | ~ (l1_struct_0 @ sk_B)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['109', '114'])).
% 0.86/1.04  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('117', plain,
% 0.86/1.04      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          != (k2_struct_0 @ sk_B)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('demod', [status(thm)], ['115', '116'])).
% 0.86/1.04  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('120', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.86/1.04      inference('sup+', [status(thm)], ['2', '3'])).
% 0.86/1.04  thf('121', plain,
% 0.86/1.04      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.86/1.04          != (k2_relat_1 @ sk_C)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.86/1.04  thf('122', plain,
% 0.86/1.04      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['108', '121'])).
% 0.86/1.04  thf('123', plain,
% 0.86/1.04      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['107', '122'])).
% 0.86/1.04  thf('124', plain,
% 0.86/1.04      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.86/1.04         | ~ (v1_relat_1 @ sk_C)
% 0.86/1.04         | ~ (v1_funct_1 @ sk_C)
% 0.86/1.04         | ~ (v2_funct_1 @ sk_C)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['104', '123'])).
% 0.86/1.04  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 0.86/1.04      inference('sup-', [status(thm)], ['98', '99'])).
% 0.86/1.04  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('128', plain,
% 0.86/1.04      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.86/1.04         <= (~
% 0.86/1.04             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04                = (k2_struct_0 @ sk_B))))),
% 0.86/1.04      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.86/1.04  thf('129', plain,
% 0.86/1.04      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          = (k2_struct_0 @ sk_B)))),
% 0.86/1.04      inference('simplify', [status(thm)], ['128'])).
% 0.86/1.04  thf('130', plain,
% 0.86/1.04      (~
% 0.86/1.04       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          = (k2_struct_0 @ sk_A))) | 
% 0.86/1.04       ~
% 0.86/1.04       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          = (k2_struct_0 @ sk_B)))),
% 0.86/1.04      inference('split', [status(esa)], ['37'])).
% 0.86/1.04  thf('131', plain,
% 0.86/1.04      (~
% 0.86/1.04       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.86/1.04          = (k2_struct_0 @ sk_A)))),
% 0.86/1.04      inference('sat_resolution*', [status(thm)], ['129', '130'])).
% 0.86/1.04  thf('132', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.86/1.04      inference('simpl_trail', [status(thm)], ['103', '131'])).
% 0.86/1.04  thf('133', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.86/1.04      inference('simplify_reflect-', [status(thm)], ['35', '132'])).
% 0.86/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.86/1.04  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.86/1.04  thf('135', plain, ($false),
% 0.86/1.04      inference('demod', [status(thm)], ['13', '133', '134'])).
% 0.86/1.04  
% 0.86/1.04  % SZS output end Refutation
% 0.86/1.04  
% 0.86/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
