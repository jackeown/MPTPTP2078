%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rGoTJ7zb4D

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:02 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 542 expanded)
%              Number of leaves         :   45 ( 178 expanded)
%              Depth                    :   17
%              Number of atoms          : 2007 (13742 expanded)
%              Number of equality atoms :  160 ( 763 expanded)
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

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

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

thf('47',plain,(
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

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('62',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('75',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','56','66','67','75'])).

thf('77',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('79',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('80',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('82',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k3_relset_1 @ X16 @ X17 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('83',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('86',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('89',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','93'])).

thf('95',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','77','94'])).

thf('96',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('98',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('99',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('101',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('102',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('110',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
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

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['126','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('141',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('150',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125','136','137','138','150'])).

thf('152',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('156',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('157',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','162'])).

thf('164',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('167',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('169',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','169'])).

thf('171',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','170'])).

thf('172',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('174',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['172','173'])).

thf('175',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['95','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','175'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('177',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('178',plain,(
    $false ),
    inference(demod,[status(thm)],['10','176','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rGoTJ7zb4D
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.98/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.20  % Solved by: fo/fo7.sh
% 0.98/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.20  % done 427 iterations in 0.735s
% 0.98/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.20  % SZS output start Refutation
% 0.98/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.98/1.20  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.98/1.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.20  thf(sk_C_type, type, sk_C: $i).
% 0.98/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.98/1.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.98/1.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.98/1.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.98/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.20  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.98/1.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.98/1.20  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.98/1.20  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.98/1.20  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.98/1.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.98/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.98/1.20  thf(sk_B_type, type, sk_B: $i).
% 0.98/1.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.98/1.20  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.98/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.98/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.98/1.20  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.98/1.20  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.98/1.20  thf(t62_tops_2, conjecture,
% 0.98/1.20    (![A:$i]:
% 0.98/1.20     ( ( l1_struct_0 @ A ) =>
% 0.98/1.20       ( ![B:$i]:
% 0.98/1.20         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.98/1.20           ( ![C:$i]:
% 0.98/1.20             ( ( ( v1_funct_1 @ C ) & 
% 0.98/1.20                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.98/1.20                 ( m1_subset_1 @
% 0.98/1.20                   C @ 
% 0.98/1.20                   ( k1_zfmisc_1 @
% 0.98/1.20                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.98/1.20               ( ( ( ( k2_relset_1 @
% 0.98/1.20                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.98/1.20                     ( k2_struct_0 @ B ) ) & 
% 0.98/1.20                   ( v2_funct_1 @ C ) ) =>
% 0.98/1.20                 ( ( ( k1_relset_1 @
% 0.98/1.20                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.98/1.20                       ( k2_tops_2 @
% 0.98/1.20                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.98/1.20                     ( k2_struct_0 @ B ) ) & 
% 0.98/1.20                   ( ( k2_relset_1 @
% 0.98/1.20                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.98/1.20                       ( k2_tops_2 @
% 0.98/1.20                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.98/1.20                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.98/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.20    (~( ![A:$i]:
% 0.98/1.20        ( ( l1_struct_0 @ A ) =>
% 0.98/1.20          ( ![B:$i]:
% 0.98/1.20            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.98/1.20              ( ![C:$i]:
% 0.98/1.20                ( ( ( v1_funct_1 @ C ) & 
% 0.98/1.20                    ( v1_funct_2 @
% 0.98/1.20                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.98/1.20                    ( m1_subset_1 @
% 0.98/1.20                      C @ 
% 0.98/1.20                      ( k1_zfmisc_1 @
% 0.98/1.20                        ( k2_zfmisc_1 @
% 0.98/1.20                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.98/1.20                  ( ( ( ( k2_relset_1 @
% 0.98/1.20                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.98/1.20                        ( k2_struct_0 @ B ) ) & 
% 0.98/1.20                      ( v2_funct_1 @ C ) ) =>
% 0.98/1.20                    ( ( ( k1_relset_1 @
% 0.98/1.20                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.98/1.20                          ( k2_tops_2 @
% 0.98/1.20                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.98/1.20                        ( k2_struct_0 @ B ) ) & 
% 0.98/1.20                      ( ( k2_relset_1 @
% 0.98/1.20                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.98/1.20                          ( k2_tops_2 @
% 0.98/1.20                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.98/1.20                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.98/1.20    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.98/1.20  thf('0', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf(redefinition_k2_relset_1, axiom,
% 0.98/1.20    (![A:$i,B:$i,C:$i]:
% 0.98/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.98/1.20  thf('1', plain,
% 0.98/1.20      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.98/1.20         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.98/1.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.98/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.98/1.20  thf('2', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('sup-', [status(thm)], ['0', '1'])).
% 0.98/1.20  thf('3', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf(fc5_struct_0, axiom,
% 0.98/1.20    (![A:$i]:
% 0.98/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.98/1.20       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.98/1.20  thf('5', plain,
% 0.98/1.20      (![X27 : $i]:
% 0.98/1.20         (~ (v1_xboole_0 @ (k2_struct_0 @ X27))
% 0.98/1.20          | ~ (l1_struct_0 @ X27)
% 0.98/1.20          | (v2_struct_0 @ X27))),
% 0.98/1.20      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.98/1.20  thf('6', plain,
% 0.98/1.20      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.98/1.20        | (v2_struct_0 @ sk_B)
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup-', [status(thm)], ['4', '5'])).
% 0.98/1.20  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('8', plain,
% 0.98/1.20      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.98/1.20      inference('demod', [status(thm)], ['6', '7'])).
% 0.98/1.20  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('clc', [status(thm)], ['8', '9'])).
% 0.98/1.20  thf(d3_struct_0, axiom,
% 0.98/1.20    (![A:$i]:
% 0.98/1.20     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.98/1.20  thf('11', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('12', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf(d1_funct_2, axiom,
% 0.98/1.20    (![A:$i,B:$i,C:$i]:
% 0.98/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.20       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.98/1.20           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.98/1.20             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.98/1.20         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.98/1.20           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.98/1.20             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.98/1.20  thf(zf_stmt_1, axiom,
% 0.98/1.20    (![B:$i,A:$i]:
% 0.98/1.20     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.98/1.20       ( zip_tseitin_0 @ B @ A ) ))).
% 0.98/1.20  thf('13', plain,
% 0.98/1.20      (![X18 : $i, X19 : $i]:
% 0.98/1.20         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.98/1.20  thf('14', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.98/1.20  thf(zf_stmt_3, axiom,
% 0.98/1.20    (![C:$i,B:$i,A:$i]:
% 0.98/1.20     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.98/1.20       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.98/1.20  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.98/1.20  thf(zf_stmt_5, axiom,
% 0.98/1.20    (![A:$i,B:$i,C:$i]:
% 0.98/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.20       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.98/1.20         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.98/1.20           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.98/1.20             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.98/1.20  thf('15', plain,
% 0.98/1.20      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.98/1.20         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.98/1.20          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.98/1.20          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.98/1.20  thf('16', plain,
% 0.98/1.20      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.98/1.20        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['14', '15'])).
% 0.98/1.20  thf('17', plain,
% 0.98/1.20      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.98/1.20        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['13', '16'])).
% 0.98/1.20  thf('18', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('19', plain,
% 0.98/1.20      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.98/1.20         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.98/1.20          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.98/1.20          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.98/1.20  thf('20', plain,
% 0.98/1.20      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.98/1.20        | ((u1_struct_0 @ sk_A)
% 0.98/1.20            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['18', '19'])).
% 0.98/1.20  thf('21', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf(redefinition_k1_relset_1, axiom,
% 0.98/1.20    (![A:$i,B:$i,C:$i]:
% 0.98/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.20       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.98/1.20  thf('22', plain,
% 0.98/1.20      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.98/1.20         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.98/1.20          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.98/1.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.98/1.20  thf('23', plain,
% 0.98/1.20      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k1_relat_1 @ sk_C))),
% 0.98/1.20      inference('sup-', [status(thm)], ['21', '22'])).
% 0.98/1.20  thf('24', plain,
% 0.98/1.20      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.98/1.20        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.98/1.20      inference('demod', [status(thm)], ['20', '23'])).
% 0.98/1.20  thf('25', plain,
% 0.98/1.20      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.98/1.20        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['17', '24'])).
% 0.98/1.20  thf('26', plain,
% 0.98/1.20      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B)
% 0.98/1.20        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.98/1.20      inference('sup+', [status(thm)], ['12', '25'])).
% 0.98/1.20  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('29', plain,
% 0.98/1.20      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.98/1.20        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.98/1.20      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.98/1.20  thf('30', plain,
% 0.98/1.20      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_A)
% 0.98/1.20        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.98/1.20      inference('sup+', [status(thm)], ['11', '29'])).
% 0.98/1.20  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('32', plain,
% 0.98/1.20      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.98/1.20        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.98/1.20      inference('demod', [status(thm)], ['30', '31'])).
% 0.98/1.20  thf('33', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('34', plain,
% 0.98/1.20      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          != (k2_struct_0 @ sk_B))
% 0.98/1.20        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20            != (k2_struct_0 @ sk_A)))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('35', plain,
% 0.98/1.20      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          != (k2_struct_0 @ sk_A)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_A))))),
% 0.98/1.20      inference('split', [status(esa)], ['34'])).
% 0.98/1.20  thf('36', plain,
% 0.98/1.20      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20           != (k2_struct_0 @ sk_A))
% 0.98/1.20         | ~ (l1_struct_0 @ sk_B)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_A))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['33', '35'])).
% 0.98/1.20  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('38', plain,
% 0.98/1.20      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          != (k2_struct_0 @ sk_A)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_A))))),
% 0.98/1.20      inference('demod', [status(thm)], ['36', '37'])).
% 0.98/1.20  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('40', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('41', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('42', plain,
% 0.98/1.20      (((m1_subset_1 @ sk_C @ 
% 0.98/1.20         (k1_zfmisc_1 @ 
% 0.98/1.20          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['40', '41'])).
% 0.98/1.20  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('44', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('demod', [status(thm)], ['42', '43'])).
% 0.98/1.20  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('46', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.98/1.20      inference('demod', [status(thm)], ['44', '45'])).
% 0.98/1.20  thf(d4_tops_2, axiom,
% 0.98/1.20    (![A:$i,B:$i,C:$i]:
% 0.98/1.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.98/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.20       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.98/1.20         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.98/1.20  thf('47', plain,
% 0.98/1.20      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.98/1.20         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.98/1.20          | ~ (v2_funct_1 @ X30)
% 0.98/1.20          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.98/1.20          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.98/1.20          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.98/1.20          | ~ (v1_funct_1 @ X30))),
% 0.98/1.20      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.98/1.20  thf('48', plain,
% 0.98/1.20      ((~ (v1_funct_1 @ sk_C)
% 0.98/1.20        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.98/1.20        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20            = (k2_funct_1 @ sk_C))
% 0.98/1.20        | ~ (v2_funct_1 @ sk_C)
% 0.98/1.20        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20            != (k2_relat_1 @ sk_C)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['46', '47'])).
% 0.98/1.20  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('50', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('51', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('52', plain,
% 0.98/1.20      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['50', '51'])).
% 0.98/1.20  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('54', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('demod', [status(thm)], ['52', '53'])).
% 0.98/1.20  thf('55', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('56', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['54', '55'])).
% 0.98/1.20  thf('57', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf(cc2_relat_1, axiom,
% 0.98/1.20    (![A:$i]:
% 0.98/1.20     ( ( v1_relat_1 @ A ) =>
% 0.98/1.20       ( ![B:$i]:
% 0.98/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.98/1.20  thf('58', plain,
% 0.98/1.20      (![X0 : $i, X1 : $i]:
% 0.98/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.98/1.20          | (v1_relat_1 @ X0)
% 0.98/1.20          | ~ (v1_relat_1 @ X1))),
% 0.98/1.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.98/1.20  thf('59', plain,
% 0.98/1.20      ((~ (v1_relat_1 @ 
% 0.98/1.20           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.98/1.20        | (v1_relat_1 @ sk_C))),
% 0.98/1.20      inference('sup-', [status(thm)], ['57', '58'])).
% 0.98/1.20  thf(fc6_relat_1, axiom,
% 0.98/1.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.98/1.20  thf('60', plain,
% 0.98/1.20      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.98/1.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.98/1.20  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.98/1.20      inference('demod', [status(thm)], ['59', '60'])).
% 0.98/1.20  thf(d9_funct_1, axiom,
% 0.98/1.20    (![A:$i]:
% 0.98/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.98/1.20       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.98/1.20  thf('62', plain,
% 0.98/1.20      (![X4 : $i]:
% 0.98/1.20         (~ (v2_funct_1 @ X4)
% 0.98/1.20          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 0.98/1.20          | ~ (v1_funct_1 @ X4)
% 0.98/1.20          | ~ (v1_relat_1 @ X4))),
% 0.98/1.20      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.98/1.20  thf('63', plain,
% 0.98/1.20      ((~ (v1_funct_1 @ sk_C)
% 0.98/1.20        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.98/1.20        | ~ (v2_funct_1 @ sk_C))),
% 0.98/1.20      inference('sup-', [status(thm)], ['61', '62'])).
% 0.98/1.20  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('66', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.98/1.20  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('68', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('69', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('70', plain,
% 0.98/1.20      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20          = (k2_struct_0 @ sk_B))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['68', '69'])).
% 0.98/1.20  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('72', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('demod', [status(thm)], ['70', '71'])).
% 0.98/1.20  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('74', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('75', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20         = (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.98/1.20  thf('76', plain,
% 0.98/1.20      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20          = (k4_relat_1 @ sk_C))
% 0.98/1.20        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.98/1.20      inference('demod', [status(thm)], ['48', '49', '56', '66', '67', '75'])).
% 0.98/1.20  thf('77', plain,
% 0.98/1.20      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20         = (k4_relat_1 @ sk_C))),
% 0.98/1.20      inference('simplify', [status(thm)], ['76'])).
% 0.98/1.20  thf('78', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf(dt_k3_relset_1, axiom,
% 0.98/1.20    (![A:$i,B:$i,C:$i]:
% 0.98/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.20       ( m1_subset_1 @
% 0.98/1.20         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.98/1.20         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.98/1.20  thf('79', plain,
% 0.98/1.20      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.98/1.20         ((m1_subset_1 @ (k3_relset_1 @ X6 @ X7 @ X8) @ 
% 0.98/1.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.98/1.20          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.98/1.20      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.98/1.20  thf('80', plain,
% 0.98/1.20      ((m1_subset_1 @ 
% 0.98/1.20        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['78', '79'])).
% 0.98/1.20  thf('81', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf(redefinition_k3_relset_1, axiom,
% 0.98/1.20    (![A:$i,B:$i,C:$i]:
% 0.98/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.20       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.98/1.20  thf('82', plain,
% 0.98/1.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.98/1.20         (((k3_relset_1 @ X16 @ X17 @ X15) = (k4_relat_1 @ X15))
% 0.98/1.20          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.98/1.20      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.98/1.20  thf('83', plain,
% 0.98/1.20      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k4_relat_1 @ sk_C))),
% 0.98/1.20      inference('sup-', [status(thm)], ['81', '82'])).
% 0.98/1.20  thf('84', plain,
% 0.98/1.20      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.98/1.20      inference('demod', [status(thm)], ['80', '83'])).
% 0.98/1.20  thf('85', plain,
% 0.98/1.20      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.98/1.20         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.98/1.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.98/1.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.98/1.20  thf('86', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['84', '85'])).
% 0.98/1.20  thf('87', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.98/1.20  thf(t55_funct_1, axiom,
% 0.98/1.20    (![A:$i]:
% 0.98/1.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.98/1.20       ( ( v2_funct_1 @ A ) =>
% 0.98/1.20         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.98/1.20           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.98/1.20  thf('88', plain,
% 0.98/1.20      (![X5 : $i]:
% 0.98/1.20         (~ (v2_funct_1 @ X5)
% 0.98/1.20          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.98/1.20          | ~ (v1_funct_1 @ X5)
% 0.98/1.20          | ~ (v1_relat_1 @ X5))),
% 0.98/1.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.98/1.20  thf('89', plain,
% 0.98/1.20      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.98/1.20        | ~ (v1_relat_1 @ sk_C)
% 0.98/1.20        | ~ (v1_funct_1 @ sk_C)
% 0.98/1.20        | ~ (v2_funct_1 @ sk_C))),
% 0.98/1.20      inference('sup+', [status(thm)], ['87', '88'])).
% 0.98/1.20  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.98/1.20      inference('demod', [status(thm)], ['59', '60'])).
% 0.98/1.20  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('93', plain,
% 0.98/1.20      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.98/1.20      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.98/1.20  thf('94', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['86', '93'])).
% 0.98/1.20  thf('95', plain,
% 0.98/1.20      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_A))))),
% 0.98/1.20      inference('demod', [status(thm)], ['38', '39', '77', '94'])).
% 0.98/1.20  thf('96', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('97', plain,
% 0.98/1.20      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.98/1.20      inference('demod', [status(thm)], ['80', '83'])).
% 0.98/1.20  thf('98', plain,
% 0.98/1.20      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.98/1.20         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.98/1.20          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.98/1.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.98/1.20  thf('99', plain,
% 0.98/1.20      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['97', '98'])).
% 0.98/1.20  thf('100', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.98/1.20  thf('101', plain,
% 0.98/1.20      (![X5 : $i]:
% 0.98/1.20         (~ (v2_funct_1 @ X5)
% 0.98/1.20          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.98/1.20          | ~ (v1_funct_1 @ X5)
% 0.98/1.20          | ~ (v1_relat_1 @ X5))),
% 0.98/1.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.98/1.20  thf('102', plain,
% 0.98/1.20      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.98/1.20        | ~ (v1_relat_1 @ sk_C)
% 0.98/1.20        | ~ (v1_funct_1 @ sk_C)
% 0.98/1.20        | ~ (v2_funct_1 @ sk_C))),
% 0.98/1.20      inference('sup+', [status(thm)], ['100', '101'])).
% 0.98/1.20  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.98/1.20      inference('demod', [status(thm)], ['59', '60'])).
% 0.98/1.20  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('106', plain,
% 0.98/1.20      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.98/1.20      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.98/1.20  thf('107', plain,
% 0.98/1.20      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['99', '106'])).
% 0.98/1.20  thf('108', plain,
% 0.98/1.20      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['96', '107'])).
% 0.98/1.20  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('110', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('111', plain,
% 0.98/1.20      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.98/1.20  thf('112', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('113', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('114', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('115', plain,
% 0.98/1.20      (((m1_subset_1 @ sk_C @ 
% 0.98/1.20         (k1_zfmisc_1 @ 
% 0.98/1.20          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_A))),
% 0.98/1.20      inference('sup+', [status(thm)], ['113', '114'])).
% 0.98/1.20  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('117', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.98/1.20      inference('demod', [status(thm)], ['115', '116'])).
% 0.98/1.20  thf('118', plain,
% 0.98/1.20      (((m1_subset_1 @ sk_C @ 
% 0.98/1.20         (k1_zfmisc_1 @ 
% 0.98/1.20          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['112', '117'])).
% 0.98/1.20  thf('119', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('120', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('demod', [status(thm)], ['118', '119'])).
% 0.98/1.20  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('122', plain,
% 0.98/1.20      ((m1_subset_1 @ sk_C @ 
% 0.98/1.20        (k1_zfmisc_1 @ 
% 0.98/1.20         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.98/1.20      inference('demod', [status(thm)], ['120', '121'])).
% 0.98/1.20  thf('123', plain,
% 0.98/1.20      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.98/1.20         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.98/1.20          | ~ (v2_funct_1 @ X30)
% 0.98/1.20          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 0.98/1.20          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.98/1.20          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.98/1.20          | ~ (v1_funct_1 @ X30))),
% 0.98/1.20      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.98/1.20  thf('124', plain,
% 0.98/1.20      ((~ (v1_funct_1 @ sk_C)
% 0.98/1.20        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.98/1.20        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20            = (k2_funct_1 @ sk_C))
% 0.98/1.20        | ~ (v2_funct_1 @ sk_C)
% 0.98/1.20        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20            != (k2_relat_1 @ sk_C)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['122', '123'])).
% 0.98/1.20  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('126', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('127', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('128', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('129', plain,
% 0.98/1.20      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_A))),
% 0.98/1.20      inference('sup+', [status(thm)], ['127', '128'])).
% 0.98/1.20  thf('130', plain, ((l1_struct_0 @ sk_A)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('131', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.98/1.20      inference('demod', [status(thm)], ['129', '130'])).
% 0.98/1.20  thf('132', plain,
% 0.98/1.20      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['126', '131'])).
% 0.98/1.20  thf('133', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('134', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('demod', [status(thm)], ['132', '133'])).
% 0.98/1.20  thf('135', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('136', plain,
% 0.98/1.20      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['134', '135'])).
% 0.98/1.20  thf('137', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.98/1.20  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('139', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('140', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('141', plain,
% 0.98/1.20      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('142', plain,
% 0.98/1.20      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20          = (k2_struct_0 @ sk_B))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_A))),
% 0.98/1.20      inference('sup+', [status(thm)], ['140', '141'])).
% 0.98/1.20  thf('143', plain, ((l1_struct_0 @ sk_A)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('144', plain,
% 0.98/1.20      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('demod', [status(thm)], ['142', '143'])).
% 0.98/1.20  thf('145', plain,
% 0.98/1.20      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20          = (k2_struct_0 @ sk_B))
% 0.98/1.20        | ~ (l1_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['139', '144'])).
% 0.98/1.20  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('147', plain,
% 0.98/1.20      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.98/1.20         = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('demod', [status(thm)], ['145', '146'])).
% 0.98/1.20  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('150', plain,
% 0.98/1.20      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20         = (k2_relat_1 @ sk_C))),
% 0.98/1.20      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.98/1.20  thf('151', plain,
% 0.98/1.20      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20          = (k4_relat_1 @ sk_C))
% 0.98/1.20        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.98/1.20      inference('demod', [status(thm)],
% 0.98/1.20                ['124', '125', '136', '137', '138', '150'])).
% 0.98/1.20  thf('152', plain,
% 0.98/1.20      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.98/1.20         = (k4_relat_1 @ sk_C))),
% 0.98/1.20      inference('simplify', [status(thm)], ['151'])).
% 0.98/1.20  thf('153', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('154', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('155', plain,
% 0.98/1.20      (![X26 : $i]:
% 0.98/1.20         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.98/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.98/1.20  thf('156', plain,
% 0.98/1.20      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          != (k2_struct_0 @ sk_B)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('split', [status(esa)], ['34'])).
% 0.98/1.20  thf('157', plain,
% 0.98/1.20      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20           != (k2_struct_0 @ sk_B))
% 0.98/1.20         | ~ (l1_struct_0 @ sk_B)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['155', '156'])).
% 0.98/1.20  thf('158', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('159', plain,
% 0.98/1.20      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          != (k2_struct_0 @ sk_B)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('demod', [status(thm)], ['157', '158'])).
% 0.98/1.20  thf('160', plain,
% 0.98/1.20      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20           != (k2_struct_0 @ sk_B))
% 0.98/1.20         | ~ (l1_struct_0 @ sk_A)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['154', '159'])).
% 0.98/1.20  thf('161', plain, ((l1_struct_0 @ sk_A)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('162', plain,
% 0.98/1.20      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          != (k2_struct_0 @ sk_B)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('demod', [status(thm)], ['160', '161'])).
% 0.98/1.20  thf('163', plain,
% 0.98/1.20      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20           != (k2_struct_0 @ sk_B))
% 0.98/1.20         | ~ (l1_struct_0 @ sk_B)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['153', '162'])).
% 0.98/1.20  thf('164', plain, ((l1_struct_0 @ sk_B)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('165', plain,
% 0.98/1.20      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          != (k2_struct_0 @ sk_B)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('demod', [status(thm)], ['163', '164'])).
% 0.98/1.20  thf('166', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('167', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.98/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.20  thf('169', plain,
% 0.98/1.20      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.98/1.20          != (k2_relat_1 @ sk_C)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 0.98/1.20  thf('170', plain,
% 0.98/1.20      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['152', '169'])).
% 0.98/1.20  thf('171', plain,
% 0.98/1.20      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.98/1.20         <= (~
% 0.98/1.20             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20                = (k2_struct_0 @ sk_B))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['111', '170'])).
% 0.98/1.20  thf('172', plain,
% 0.98/1.20      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          = (k2_struct_0 @ sk_B)))),
% 0.98/1.20      inference('simplify', [status(thm)], ['171'])).
% 0.98/1.20  thf('173', plain,
% 0.98/1.20      (~
% 0.98/1.20       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          = (k2_struct_0 @ sk_A))) | 
% 0.98/1.20       ~
% 0.98/1.20       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          = (k2_struct_0 @ sk_B)))),
% 0.98/1.20      inference('split', [status(esa)], ['34'])).
% 0.98/1.20  thf('174', plain,
% 0.98/1.20      (~
% 0.98/1.20       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.98/1.20          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.98/1.20          = (k2_struct_0 @ sk_A)))),
% 0.98/1.20      inference('sat_resolution*', [status(thm)], ['172', '173'])).
% 0.98/1.20  thf('175', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.98/1.20      inference('simpl_trail', [status(thm)], ['95', '174'])).
% 0.98/1.20  thf('176', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.98/1.20      inference('simplify_reflect-', [status(thm)], ['32', '175'])).
% 0.98/1.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.98/1.20  thf('177', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.98/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.98/1.20  thf('178', plain, ($false),
% 0.98/1.20      inference('demod', [status(thm)], ['10', '176', '177'])).
% 0.98/1.20  
% 0.98/1.20  % SZS output end Refutation
% 0.98/1.20  
% 0.98/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
