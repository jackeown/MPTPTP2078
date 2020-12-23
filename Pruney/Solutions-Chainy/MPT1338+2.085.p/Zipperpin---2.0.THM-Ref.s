%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WdeCxbXmui

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:02 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 546 expanded)
%              Number of leaves         :   45 ( 179 expanded)
%              Depth                    :   17
%              Number of atoms          : 2030 (13772 expanded)
%              Number of equality atoms :  161 ( 765 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('43',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

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

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('78',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','59','69','70','78'])).

thf('80',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('82',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('83',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('85',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k3_relset_1 @ X16 @ X17 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('86',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('89',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['89','96'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','80','97'])).

thf('99',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('101',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('102',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('104',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('105',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','109'])).

thf('111',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['115','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['129','134'])).

thf('136',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['142','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('153',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128','139','140','141','153'])).

thf('155',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('158',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('159',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['37'])).

thf('160',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','162'])).

thf('164',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('170',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('172',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['155','172'])).

thf('174',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','173'])).

thf('175',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['37'])).

thf('177',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['175','176'])).

thf('178',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['98','177'])).

thf('179',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','178'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('180',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('181',plain,(
    $false ),
    inference(demod,[status(thm)],['13','179','180'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WdeCxbXmui
% 0.13/0.36  % Computer   : n011.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:35:27 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 427 iterations in 0.697s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.14  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.90/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.90/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.14  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.90/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.14  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.90/1.14  thf(t62_tops_2, conjecture,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( l1_struct_0 @ A ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.14                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.14                 ( m1_subset_1 @
% 0.90/1.14                   C @ 
% 0.90/1.14                   ( k1_zfmisc_1 @
% 0.90/1.14                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.14               ( ( ( ( k2_relset_1 @
% 0.90/1.14                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.90/1.14                     ( k2_struct_0 @ B ) ) & 
% 0.90/1.14                   ( v2_funct_1 @ C ) ) =>
% 0.90/1.14                 ( ( ( k1_relset_1 @
% 0.90/1.14                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.90/1.14                       ( k2_tops_2 @
% 0.90/1.14                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.90/1.14                     ( k2_struct_0 @ B ) ) & 
% 0.90/1.14                   ( ( k2_relset_1 @
% 0.90/1.14                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.90/1.14                       ( k2_tops_2 @
% 0.90/1.14                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.90/1.14                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i]:
% 0.90/1.14        ( ( l1_struct_0 @ A ) =>
% 0.90/1.14          ( ![B:$i]:
% 0.90/1.14            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.90/1.14              ( ![C:$i]:
% 0.90/1.14                ( ( ( v1_funct_1 @ C ) & 
% 0.90/1.14                    ( v1_funct_2 @
% 0.90/1.14                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.90/1.14                    ( m1_subset_1 @
% 0.90/1.14                      C @ 
% 0.90/1.14                      ( k1_zfmisc_1 @
% 0.90/1.14                        ( k2_zfmisc_1 @
% 0.90/1.14                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.90/1.14                  ( ( ( ( k2_relset_1 @
% 0.90/1.14                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.90/1.14                        ( k2_struct_0 @ B ) ) & 
% 0.90/1.14                      ( v2_funct_1 @ C ) ) =>
% 0.90/1.14                    ( ( ( k1_relset_1 @
% 0.90/1.14                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.90/1.14                          ( k2_tops_2 @
% 0.90/1.14                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.90/1.14                        ( k2_struct_0 @ B ) ) & 
% 0.90/1.14                      ( ( k2_relset_1 @
% 0.90/1.14                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.90/1.14                          ( k2_tops_2 @
% 0.90/1.14                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.90/1.14                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('1', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.90/1.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf(d3_struct_0, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf(fc2_struct_0, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.14       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (![X27 : $i]:
% 0.90/1.14         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 0.90/1.14          | ~ (l1_struct_0 @ X27)
% 0.90/1.14          | (v2_struct_0 @ X27))),
% 0.90/1.14      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.90/1.14  thf('7', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | (v2_struct_0 @ X0)
% 0.90/1.14          | ~ (l1_struct_0 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         ((v2_struct_0 @ X0)
% 0.90/1.14          | ~ (l1_struct_0 @ X0)
% 0.90/1.14          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['7'])).
% 0.90/1.14  thf('9', plain,
% 0.90/1.14      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B)
% 0.90/1.14        | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['4', '8'])).
% 0.90/1.14  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('11', plain,
% 0.90/1.14      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['9', '10'])).
% 0.90/1.14  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('clc', [status(thm)], ['11', '12'])).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf(d1_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_1, axiom,
% 0.90/1.14    (![B:$i,A:$i]:
% 0.90/1.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.14       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      (![X18 : $i, X19 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('17', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_3, axiom,
% 0.90/1.14    (![C:$i,B:$i,A:$i]:
% 0.90/1.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_5, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.90/1.14          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.90/1.14          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.90/1.14        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.14  thf('20', plain,
% 0.90/1.14      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.90/1.14        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['16', '19'])).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.14         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.90/1.14          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.90/1.14          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.90/1.14        | ((u1_struct_0 @ sk_A)
% 0.90/1.14            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.90/1.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['24', '25'])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.90/1.14        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '26'])).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.90/1.14        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['20', '27'])).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B)
% 0.90/1.14        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['15', '28'])).
% 0.90/1.14  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.90/1.14        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_A)
% 0.90/1.14        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['14', '32'])).
% 0.90/1.14  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.90/1.14        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['33', '34'])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('37', plain,
% 0.90/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          != (k2_struct_0 @ sk_B))
% 0.90/1.14        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14            != (k2_struct_0 @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('38', plain,
% 0.90/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          != (k2_struct_0 @ sk_A)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_A))))),
% 0.90/1.14      inference('split', [status(esa)], ['37'])).
% 0.90/1.14  thf('39', plain,
% 0.90/1.14      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14           != (k2_struct_0 @ sk_A))
% 0.90/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['36', '38'])).
% 0.90/1.14  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('41', plain,
% 0.90/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          != (k2_struct_0 @ sk_A)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_A))))),
% 0.90/1.14      inference('demod', [status(thm)], ['39', '40'])).
% 0.90/1.14  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_C @ 
% 0.90/1.14         (k1_zfmisc_1 @ 
% 0.90/1.14          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['43', '44'])).
% 0.90/1.14  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('47', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['45', '46'])).
% 0.90/1.14  thf('48', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('49', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.90/1.14      inference('demod', [status(thm)], ['47', '48'])).
% 0.90/1.14  thf(d4_tops_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.14         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.90/1.14          | ~ (v2_funct_1 @ X30)
% 0.90/1.14          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.90/1.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.90/1.14          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.90/1.14          | ~ (v1_funct_1 @ X30))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.90/1.14        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14            = (k2_funct_1 @ sk_C))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.14        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14            != (k2_relat_1 @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.14  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('54', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('55', plain,
% 0.90/1.14      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['53', '54'])).
% 0.90/1.14  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('57', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['55', '56'])).
% 0.90/1.14  thf('58', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['57', '58'])).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(cc2_relat_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( v1_relat_1 @ A ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.90/1.14          | (v1_relat_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.14  thf('62', plain,
% 0.90/1.14      ((~ (v1_relat_1 @ 
% 0.90/1.14           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.90/1.14        | (v1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['60', '61'])).
% 0.90/1.14  thf(fc6_relat_1, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.14  thf('63', plain,
% 0.90/1.14      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.14  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['62', '63'])).
% 0.90/1.14  thf(d9_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      (![X4 : $i]:
% 0.90/1.14         (~ (v2_funct_1 @ X4)
% 0.90/1.14          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.90/1.14          | ~ (v1_funct_1 @ X4)
% 0.90/1.14          | ~ (v1_relat_1 @ X4))),
% 0.90/1.14      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.90/1.14  thf('66', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['64', '65'])).
% 0.90/1.14  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('69', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.90/1.14  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('71', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('72', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14          = (k2_struct_0 @ sk_B))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['71', '72'])).
% 0.90/1.14  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('75', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['73', '74'])).
% 0.90/1.14  thf('76', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('77', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('78', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14         = (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14          = (k4_relat_1 @ sk_C))
% 0.90/1.14        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)], ['51', '52', '59', '69', '70', '78'])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14         = (k4_relat_1 @ sk_C))),
% 0.90/1.14      inference('simplify', [status(thm)], ['79'])).
% 0.90/1.14  thf('81', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(dt_k3_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( m1_subset_1 @
% 0.90/1.14         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.90/1.14         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.90/1.14  thf('82', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k3_relset_1 @ X6 @ X7 @ X8) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.90/1.14          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.90/1.14  thf('83', plain,
% 0.90/1.14      ((m1_subset_1 @ 
% 0.90/1.14        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.14  thf('84', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k3_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('85', plain,
% 0.90/1.14      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.14         (((k3_relset_1 @ X16 @ X17 @ X15) = (k4_relat_1 @ X15))
% 0.90/1.14          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.90/1.14  thf('86', plain,
% 0.90/1.14      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k4_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['84', '85'])).
% 0.90/1.14  thf('87', plain,
% 0.90/1.14      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.90/1.14      inference('demod', [status(thm)], ['83', '86'])).
% 0.90/1.14  thf('88', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.90/1.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.14  thf('89', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.14  thf('90', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.90/1.14  thf(t55_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ( v2_funct_1 @ A ) =>
% 0.90/1.14         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.90/1.14           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('91', plain,
% 0.90/1.14      (![X5 : $i]:
% 0.90/1.14         (~ (v2_funct_1 @ X5)
% 0.90/1.14          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.90/1.14          | ~ (v1_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_relat_1 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.14  thf('92', plain,
% 0.90/1.14      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['90', '91'])).
% 0.90/1.14  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['62', '63'])).
% 0.90/1.14  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('96', plain,
% 0.90/1.14      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.90/1.14  thf('97', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['89', '96'])).
% 0.90/1.14  thf('98', plain,
% 0.90/1.14      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_A))))),
% 0.90/1.14      inference('demod', [status(thm)], ['41', '42', '80', '97'])).
% 0.90/1.14  thf('99', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('100', plain,
% 0.90/1.14      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.90/1.14      inference('demod', [status(thm)], ['83', '86'])).
% 0.90/1.14  thf('101', plain,
% 0.90/1.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.90/1.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('102', plain,
% 0.90/1.14      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['100', '101'])).
% 0.90/1.14  thf('103', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.90/1.14  thf('104', plain,
% 0.90/1.14      (![X5 : $i]:
% 0.90/1.14         (~ (v2_funct_1 @ X5)
% 0.90/1.14          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.90/1.14          | ~ (v1_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_relat_1 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.14  thf('105', plain,
% 0.90/1.14      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['103', '104'])).
% 0.90/1.14  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('demod', [status(thm)], ['62', '63'])).
% 0.90/1.14  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('109', plain,
% 0.90/1.14      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.90/1.14  thf('110', plain,
% 0.90/1.14      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['102', '109'])).
% 0.90/1.14  thf('111', plain,
% 0.90/1.14      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['99', '110'])).
% 0.90/1.14  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('114', plain,
% 0.90/1.14      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.90/1.14  thf('115', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('116', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('117', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('118', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_C @ 
% 0.90/1.14         (k1_zfmisc_1 @ 
% 0.90/1.14          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.14      inference('sup+', [status(thm)], ['116', '117'])).
% 0.90/1.14  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('120', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['118', '119'])).
% 0.90/1.14  thf('121', plain,
% 0.90/1.14      (((m1_subset_1 @ sk_C @ 
% 0.90/1.14         (k1_zfmisc_1 @ 
% 0.90/1.14          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['115', '120'])).
% 0.90/1.14  thf('122', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('123', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['121', '122'])).
% 0.90/1.14  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('125', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ 
% 0.90/1.14        (k1_zfmisc_1 @ 
% 0.90/1.14         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.90/1.14      inference('demod', [status(thm)], ['123', '124'])).
% 0.90/1.14  thf('126', plain,
% 0.90/1.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.90/1.14          | ~ (v2_funct_1 @ X30)
% 0.90/1.14          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.90/1.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.90/1.14          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.90/1.14          | ~ (v1_funct_1 @ X30))),
% 0.90/1.14      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.90/1.14  thf('127', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.90/1.14        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14            = (k2_funct_1 @ sk_C))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.14        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14            != (k2_relat_1 @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['125', '126'])).
% 0.90/1.14  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('129', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('130', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('131', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('132', plain,
% 0.90/1.14      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.14      inference('sup+', [status(thm)], ['130', '131'])).
% 0.90/1.14  thf('133', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('134', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['132', '133'])).
% 0.90/1.14  thf('135', plain,
% 0.90/1.14      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['129', '134'])).
% 0.90/1.14  thf('136', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('137', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['135', '136'])).
% 0.90/1.14  thf('138', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('139', plain,
% 0.90/1.14      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['137', '138'])).
% 0.90/1.14  thf('140', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.90/1.14  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('142', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('143', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('144', plain,
% 0.90/1.14      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('145', plain,
% 0.90/1.14      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14          = (k2_struct_0 @ sk_B))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.14      inference('sup+', [status(thm)], ['143', '144'])).
% 0.90/1.14  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('147', plain,
% 0.90/1.14      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['145', '146'])).
% 0.90/1.14  thf('148', plain,
% 0.90/1.14      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14          = (k2_struct_0 @ sk_B))
% 0.90/1.14        | ~ (l1_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['142', '147'])).
% 0.90/1.14  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('150', plain,
% 0.90/1.14      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.90/1.14         = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['148', '149'])).
% 0.90/1.14  thf('151', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('152', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('153', plain,
% 0.90/1.14      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14         = (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.90/1.14  thf('154', plain,
% 0.90/1.14      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14          = (k4_relat_1 @ sk_C))
% 0.90/1.14        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['127', '128', '139', '140', '141', '153'])).
% 0.90/1.14  thf('155', plain,
% 0.90/1.14      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.90/1.14         = (k4_relat_1 @ sk_C))),
% 0.90/1.14      inference('simplify', [status(thm)], ['154'])).
% 0.90/1.14  thf('156', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('157', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('158', plain,
% 0.90/1.14      (![X26 : $i]:
% 0.90/1.14         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.90/1.14      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.14  thf('159', plain,
% 0.90/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          != (k2_struct_0 @ sk_B)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('split', [status(esa)], ['37'])).
% 0.90/1.14  thf('160', plain,
% 0.90/1.14      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14           != (k2_struct_0 @ sk_B))
% 0.90/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['158', '159'])).
% 0.90/1.14  thf('161', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('162', plain,
% 0.90/1.14      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          != (k2_struct_0 @ sk_B)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['160', '161'])).
% 0.90/1.14  thf('163', plain,
% 0.90/1.14      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14           != (k2_struct_0 @ sk_B))
% 0.90/1.14         | ~ (l1_struct_0 @ sk_A)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['157', '162'])).
% 0.90/1.14  thf('164', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('165', plain,
% 0.90/1.14      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          != (k2_struct_0 @ sk_B)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['163', '164'])).
% 0.90/1.14  thf('166', plain,
% 0.90/1.14      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14           != (k2_struct_0 @ sk_B))
% 0.90/1.14         | ~ (l1_struct_0 @ sk_B)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['156', '165'])).
% 0.90/1.14  thf('167', plain, ((l1_struct_0 @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('168', plain,
% 0.90/1.14      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          != (k2_struct_0 @ sk_B)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['166', '167'])).
% 0.90/1.14  thf('169', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('170', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('171', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.14  thf('172', plain,
% 0.90/1.14      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.90/1.14          != (k2_relat_1 @ sk_C)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 0.90/1.14  thf('173', plain,
% 0.90/1.14      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['155', '172'])).
% 0.90/1.14  thf('174', plain,
% 0.90/1.14      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.90/1.14         <= (~
% 0.90/1.14             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14                = (k2_struct_0 @ sk_B))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['114', '173'])).
% 0.90/1.14  thf('175', plain,
% 0.90/1.14      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          = (k2_struct_0 @ sk_B)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['174'])).
% 0.90/1.14  thf('176', plain,
% 0.90/1.14      (~
% 0.90/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          = (k2_struct_0 @ sk_A))) | 
% 0.90/1.14       ~
% 0.90/1.14       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          = (k2_struct_0 @ sk_B)))),
% 0.90/1.14      inference('split', [status(esa)], ['37'])).
% 0.90/1.14  thf('177', plain,
% 0.90/1.14      (~
% 0.90/1.14       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.14          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.90/1.14          = (k2_struct_0 @ sk_A)))),
% 0.90/1.14      inference('sat_resolution*', [status(thm)], ['175', '176'])).
% 0.90/1.14  thf('178', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.90/1.14      inference('simpl_trail', [status(thm)], ['98', '177'])).
% 0.90/1.14  thf('179', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['35', '178'])).
% 0.90/1.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.14  thf('180', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.14  thf('181', plain, ($false),
% 0.90/1.14      inference('demod', [status(thm)], ['13', '179', '180'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
