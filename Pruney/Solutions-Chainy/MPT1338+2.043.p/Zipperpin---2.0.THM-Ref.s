%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SKXO6yIfuP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:54 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 839 expanded)
%              Number of leaves         :   44 ( 262 expanded)
%              Depth                    :   22
%              Number of atoms          : 1957 (21022 expanded)
%              Number of equality atoms :  151 (1169 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('41',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','50','57','58','66'])).

thf('68',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('70',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','38','39','40','70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('78',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('80',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('81',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('83',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_relset_1 @ X15 @ X16 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('84',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('87',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('89',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('92',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','93','94','95'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('98',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('101',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('109',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['109','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('124',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['123','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','122','133','134','146'])).

thf('148',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','148','149'])).

thf('151',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','150'])).

thf('152',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('154',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('157',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['155','156'])).

thf('158',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['76','157'])).

thf('159',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('160',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('161',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('162',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['159','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['158','167'])).

thf('169',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('171',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    $false ),
    inference(simplify,[status(thm)],['171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SKXO6yIfuP
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:21:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.37/1.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.61  % Solved by: fo/fo7.sh
% 1.37/1.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.61  % done 503 iterations in 1.158s
% 1.37/1.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.61  % SZS output start Refutation
% 1.37/1.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.37/1.61  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 1.37/1.61  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.61  thf(sk_C_type, type, sk_C: $i).
% 1.37/1.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.37/1.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.37/1.61  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.37/1.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.37/1.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.37/1.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.37/1.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.37/1.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.37/1.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.37/1.61  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.37/1.61  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.37/1.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.37/1.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.37/1.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.37/1.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.37/1.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.37/1.61  thf(t37_relat_1, axiom,
% 1.37/1.61    (![A:$i]:
% 1.37/1.61     ( ( v1_relat_1 @ A ) =>
% 1.37/1.61       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.37/1.61         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.37/1.61  thf('0', plain,
% 1.37/1.61      (![X0 : $i]:
% 1.37/1.61         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 1.37/1.61          | ~ (v1_relat_1 @ X0))),
% 1.37/1.61      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.37/1.61  thf(d3_struct_0, axiom,
% 1.37/1.61    (![A:$i]:
% 1.37/1.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.37/1.61  thf('1', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf(t62_tops_2, conjecture,
% 1.37/1.61    (![A:$i]:
% 1.37/1.61     ( ( l1_struct_0 @ A ) =>
% 1.37/1.61       ( ![B:$i]:
% 1.37/1.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.37/1.61           ( ![C:$i]:
% 1.37/1.61             ( ( ( v1_funct_1 @ C ) & 
% 1.37/1.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.61                 ( m1_subset_1 @
% 1.37/1.61                   C @ 
% 1.37/1.61                   ( k1_zfmisc_1 @
% 1.37/1.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.61               ( ( ( ( k2_relset_1 @
% 1.37/1.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.37/1.61                     ( k2_struct_0 @ B ) ) & 
% 1.37/1.61                   ( v2_funct_1 @ C ) ) =>
% 1.37/1.61                 ( ( ( k1_relset_1 @
% 1.37/1.61                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.37/1.61                       ( k2_tops_2 @
% 1.37/1.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.37/1.61                     ( k2_struct_0 @ B ) ) & 
% 1.37/1.61                   ( ( k2_relset_1 @
% 1.37/1.61                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.37/1.61                       ( k2_tops_2 @
% 1.37/1.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.37/1.61                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.37/1.61  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.61    (~( ![A:$i]:
% 1.37/1.61        ( ( l1_struct_0 @ A ) =>
% 1.37/1.61          ( ![B:$i]:
% 1.37/1.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.37/1.61              ( ![C:$i]:
% 1.37/1.61                ( ( ( v1_funct_1 @ C ) & 
% 1.37/1.61                    ( v1_funct_2 @
% 1.37/1.61                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.37/1.61                    ( m1_subset_1 @
% 1.37/1.61                      C @ 
% 1.37/1.61                      ( k1_zfmisc_1 @
% 1.37/1.61                        ( k2_zfmisc_1 @
% 1.37/1.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.37/1.61                  ( ( ( ( k2_relset_1 @
% 1.37/1.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.37/1.61                        ( k2_struct_0 @ B ) ) & 
% 1.37/1.61                      ( v2_funct_1 @ C ) ) =>
% 1.37/1.61                    ( ( ( k1_relset_1 @
% 1.37/1.61                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.37/1.61                          ( k2_tops_2 @
% 1.37/1.61                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.37/1.61                        ( k2_struct_0 @ B ) ) & 
% 1.37/1.61                      ( ( k2_relset_1 @
% 1.37/1.61                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.37/1.61                          ( k2_tops_2 @
% 1.37/1.61                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.37/1.61                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.37/1.61    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.37/1.61  thf('2', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          != (k2_struct_0 @ sk_B))
% 1.37/1.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61            != (k2_struct_0 @ sk_A)))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('3', plain,
% 1.37/1.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          != (k2_struct_0 @ sk_A)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_A))))),
% 1.37/1.61      inference('split', [status(esa)], ['2'])).
% 1.37/1.61  thf('4', plain,
% 1.37/1.61      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61           != (k2_struct_0 @ sk_A))
% 1.37/1.61         | ~ (l1_struct_0 @ sk_B)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_A))))),
% 1.37/1.61      inference('sup-', [status(thm)], ['1', '3'])).
% 1.37/1.61  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('6', plain,
% 1.37/1.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          != (k2_struct_0 @ sk_A)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_A))))),
% 1.37/1.61      inference('demod', [status(thm)], ['4', '5'])).
% 1.37/1.61  thf('7', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf(d1_funct_2, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.37/1.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.37/1.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.37/1.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.37/1.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.37/1.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.37/1.61  thf(zf_stmt_1, axiom,
% 1.37/1.61    (![B:$i,A:$i]:
% 1.37/1.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.37/1.61       ( zip_tseitin_0 @ B @ A ) ))).
% 1.37/1.61  thf('8', plain,
% 1.37/1.61      (![X17 : $i, X18 : $i]:
% 1.37/1.61         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.37/1.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.37/1.61  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.37/1.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.37/1.61  thf('10', plain,
% 1.37/1.61      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.37/1.61      inference('sup+', [status(thm)], ['8', '9'])).
% 1.37/1.61  thf('11', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.37/1.61  thf(zf_stmt_3, axiom,
% 1.37/1.61    (![C:$i,B:$i,A:$i]:
% 1.37/1.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.37/1.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.37/1.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.37/1.61  thf(zf_stmt_5, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.37/1.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.37/1.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.37/1.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.37/1.61  thf('12', plain,
% 1.37/1.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.61         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.37/1.61          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.37/1.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.37/1.61  thf('13', plain,
% 1.37/1.61      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.37/1.61        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['11', '12'])).
% 1.37/1.61  thf('14', plain,
% 1.37/1.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.37/1.61        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['10', '13'])).
% 1.37/1.61  thf('15', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('16', plain,
% 1.37/1.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.61         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.37/1.61          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.37/1.61          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.37/1.61  thf('17', plain,
% 1.37/1.61      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.37/1.61        | ((u1_struct_0 @ sk_A)
% 1.37/1.61            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['15', '16'])).
% 1.37/1.61  thf('18', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf(redefinition_k1_relset_1, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.37/1.61  thf('19', plain,
% 1.37/1.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.61         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.37/1.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.37/1.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.37/1.61  thf('20', plain,
% 1.37/1.61      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.61  thf('21', plain,
% 1.37/1.61      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.37/1.61        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.37/1.61      inference('demod', [status(thm)], ['17', '20'])).
% 1.37/1.61  thf('22', plain,
% 1.37/1.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.37/1.61        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['14', '21'])).
% 1.37/1.61  thf('23', plain,
% 1.37/1.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B)
% 1.37/1.61        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.37/1.61      inference('sup+', [status(thm)], ['7', '22'])).
% 1.37/1.61  thf('24', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf(redefinition_k2_relset_1, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.37/1.61  thf('25', plain,
% 1.37/1.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.37/1.61         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.37/1.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.37/1.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.37/1.61  thf('26', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k2_relat_1 @ sk_C))),
% 1.37/1.61      inference('sup-', [status(thm)], ['24', '25'])).
% 1.37/1.61  thf('27', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('30', plain,
% 1.37/1.61      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.37/1.61        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.37/1.61      inference('demod', [status(thm)], ['23', '28', '29'])).
% 1.37/1.61  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf(fc5_struct_0, axiom,
% 1.37/1.61    (![A:$i]:
% 1.37/1.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.37/1.61       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.37/1.61  thf('32', plain,
% 1.37/1.61      (![X26 : $i]:
% 1.37/1.61         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 1.37/1.61          | ~ (l1_struct_0 @ X26)
% 1.37/1.61          | (v2_struct_0 @ X26))),
% 1.37/1.61      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.37/1.61  thf('33', plain,
% 1.37/1.61      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.37/1.61        | (v2_struct_0 @ sk_B)
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup-', [status(thm)], ['31', '32'])).
% 1.37/1.61  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('35', plain,
% 1.37/1.61      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.37/1.61      inference('demod', [status(thm)], ['33', '34'])).
% 1.37/1.61  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('37', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.37/1.61      inference('clc', [status(thm)], ['35', '36'])).
% 1.37/1.61  thf('38', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('clc', [status(thm)], ['30', '37'])).
% 1.37/1.61  thf('39', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('clc', [status(thm)], ['30', '37'])).
% 1.37/1.61  thf('40', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('41', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('42', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('43', plain,
% 1.37/1.61      (((m1_subset_1 @ sk_C @ 
% 1.37/1.61         (k1_zfmisc_1 @ 
% 1.37/1.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['41', '42'])).
% 1.37/1.61  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('45', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('demod', [status(thm)], ['43', '44'])).
% 1.37/1.61  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('47', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.37/1.61      inference('demod', [status(thm)], ['45', '46'])).
% 1.37/1.61  thf(d4_tops_2, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.37/1.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.37/1.61       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.37/1.61         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.37/1.61  thf('48', plain,
% 1.37/1.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.37/1.61         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.37/1.61          | ~ (v2_funct_1 @ X29)
% 1.37/1.61          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.37/1.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.37/1.61          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.37/1.61          | ~ (v1_funct_1 @ X29))),
% 1.37/1.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.37/1.61  thf('49', plain,
% 1.37/1.61      ((~ (v1_funct_1 @ sk_C)
% 1.37/1.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.37/1.61        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61            = (k2_funct_1 @ sk_C))
% 1.37/1.61        | ~ (v2_funct_1 @ sk_C)
% 1.37/1.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61            != (k2_relat_1 @ sk_C)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['47', '48'])).
% 1.37/1.61  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('51', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('52', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('53', plain,
% 1.37/1.61      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['51', '52'])).
% 1.37/1.61  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('55', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('demod', [status(thm)], ['53', '54'])).
% 1.37/1.61  thf('56', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('57', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['55', '56'])).
% 1.37/1.61  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('59', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('60', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('61', plain,
% 1.37/1.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61          = (k2_struct_0 @ sk_B))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['59', '60'])).
% 1.37/1.61  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('63', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('demod', [status(thm)], ['61', '62'])).
% 1.37/1.61  thf('64', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('66', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61         = (k2_relat_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.37/1.61  thf('67', plain,
% 1.37/1.61      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61          = (k2_funct_1 @ sk_C))
% 1.37/1.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.37/1.61      inference('demod', [status(thm)], ['49', '50', '57', '58', '66'])).
% 1.37/1.61  thf('68', plain,
% 1.37/1.61      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61         = (k2_funct_1 @ sk_C))),
% 1.37/1.61      inference('simplify', [status(thm)], ['67'])).
% 1.37/1.61  thf('69', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('clc', [status(thm)], ['30', '37'])).
% 1.37/1.61  thf('70', plain,
% 1.37/1.61      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61         = (k2_funct_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['68', '69'])).
% 1.37/1.61  thf('71', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('72', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('clc', [status(thm)], ['30', '37'])).
% 1.37/1.61  thf('73', plain,
% 1.37/1.61      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.61      inference('sup+', [status(thm)], ['71', '72'])).
% 1.37/1.61  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('75', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['73', '74'])).
% 1.37/1.61  thf('76', plain,
% 1.37/1.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_A))))),
% 1.37/1.61      inference('demod', [status(thm)], ['6', '38', '39', '40', '70', '75'])).
% 1.37/1.61  thf('77', plain,
% 1.37/1.61      (![X0 : $i]:
% 1.37/1.61         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 1.37/1.61          | ~ (v1_relat_1 @ X0))),
% 1.37/1.61      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.37/1.61  thf(d9_funct_1, axiom,
% 1.37/1.61    (![A:$i]:
% 1.37/1.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.61       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.37/1.61  thf('78', plain,
% 1.37/1.61      (![X1 : $i]:
% 1.37/1.61         (~ (v2_funct_1 @ X1)
% 1.37/1.61          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 1.37/1.61          | ~ (v1_funct_1 @ X1)
% 1.37/1.61          | ~ (v1_relat_1 @ X1))),
% 1.37/1.61      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.37/1.61  thf('79', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf(dt_k3_relset_1, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.61       ( m1_subset_1 @
% 1.37/1.61         ( k3_relset_1 @ A @ B @ C ) @ 
% 1.37/1.61         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 1.37/1.61  thf('80', plain,
% 1.37/1.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.37/1.61         ((m1_subset_1 @ (k3_relset_1 @ X5 @ X6 @ X7) @ 
% 1.37/1.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 1.37/1.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.37/1.61      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.37/1.61  thf('81', plain,
% 1.37/1.61      ((m1_subset_1 @ 
% 1.37/1.61        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.37/1.61      inference('sup-', [status(thm)], ['79', '80'])).
% 1.37/1.61  thf('82', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf(redefinition_k3_relset_1, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.61       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 1.37/1.61  thf('83', plain,
% 1.37/1.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.37/1.61         (((k3_relset_1 @ X15 @ X16 @ X14) = (k4_relat_1 @ X14))
% 1.37/1.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.37/1.61      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.37/1.61  thf('84', plain,
% 1.37/1.61      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k4_relat_1 @ sk_C))),
% 1.37/1.61      inference('sup-', [status(thm)], ['82', '83'])).
% 1.37/1.61  thf('85', plain,
% 1.37/1.61      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.37/1.61      inference('demod', [status(thm)], ['81', '84'])).
% 1.37/1.61  thf('86', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('clc', [status(thm)], ['30', '37'])).
% 1.37/1.61  thf('87', plain,
% 1.37/1.61      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.37/1.61      inference('demod', [status(thm)], ['85', '86'])).
% 1.37/1.61  thf('88', plain,
% 1.37/1.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.37/1.61         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.37/1.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.37/1.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.37/1.61  thf('89', plain,
% 1.37/1.61      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['87', '88'])).
% 1.37/1.61  thf('90', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61          (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.37/1.61        | ~ (v1_relat_1 @ sk_C)
% 1.37/1.61        | ~ (v1_funct_1 @ sk_C)
% 1.37/1.61        | ~ (v2_funct_1 @ sk_C))),
% 1.37/1.61      inference('sup+', [status(thm)], ['78', '89'])).
% 1.37/1.61  thf('91', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf(cc1_relset_1, axiom,
% 1.37/1.61    (![A:$i,B:$i,C:$i]:
% 1.37/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.37/1.61       ( v1_relat_1 @ C ) ))).
% 1.37/1.61  thf('92', plain,
% 1.37/1.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.37/1.61         ((v1_relat_1 @ X2)
% 1.37/1.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.37/1.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.37/1.61  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.37/1.61      inference('sup-', [status(thm)], ['91', '92'])).
% 1.37/1.61  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('96', plain,
% 1.37/1.61      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.37/1.61      inference('demod', [status(thm)], ['90', '93', '94', '95'])).
% 1.37/1.61  thf('97', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('clc', [status(thm)], ['30', '37'])).
% 1.37/1.61  thf('98', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('99', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('100', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          != (k2_struct_0 @ sk_B)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('split', [status(esa)], ['2'])).
% 1.37/1.61  thf('101', plain,
% 1.37/1.61      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61           != (k2_struct_0 @ sk_B))
% 1.37/1.61         | ~ (l1_struct_0 @ sk_A)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('sup-', [status(thm)], ['99', '100'])).
% 1.37/1.61  thf('102', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('103', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          != (k2_struct_0 @ sk_B)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('demod', [status(thm)], ['101', '102'])).
% 1.37/1.61  thf('104', plain,
% 1.37/1.61      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61           != (k2_struct_0 @ sk_B))
% 1.37/1.61         | ~ (l1_struct_0 @ sk_B)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('sup-', [status(thm)], ['98', '103'])).
% 1.37/1.61  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('106', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          != (k2_struct_0 @ sk_B)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('demod', [status(thm)], ['104', '105'])).
% 1.37/1.61  thf('107', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          != (k2_struct_0 @ sk_B)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('sup-', [status(thm)], ['97', '106'])).
% 1.37/1.61  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('109', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('110', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('111', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('112', plain,
% 1.37/1.61      (((m1_subset_1 @ sk_C @ 
% 1.37/1.61         (k1_zfmisc_1 @ 
% 1.37/1.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.61      inference('sup+', [status(thm)], ['110', '111'])).
% 1.37/1.61  thf('113', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('114', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.37/1.61      inference('demod', [status(thm)], ['112', '113'])).
% 1.37/1.61  thf('115', plain,
% 1.37/1.61      (((m1_subset_1 @ sk_C @ 
% 1.37/1.61         (k1_zfmisc_1 @ 
% 1.37/1.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['109', '114'])).
% 1.37/1.61  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('117', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('demod', [status(thm)], ['115', '116'])).
% 1.37/1.61  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('119', plain,
% 1.37/1.61      ((m1_subset_1 @ sk_C @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.37/1.61      inference('demod', [status(thm)], ['117', '118'])).
% 1.37/1.61  thf('120', plain,
% 1.37/1.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.37/1.61         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.37/1.61          | ~ (v2_funct_1 @ X29)
% 1.37/1.61          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.37/1.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.37/1.61          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.37/1.61          | ~ (v1_funct_1 @ X29))),
% 1.37/1.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.37/1.61  thf('121', plain,
% 1.37/1.61      ((~ (v1_funct_1 @ sk_C)
% 1.37/1.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.37/1.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61            = (k2_funct_1 @ sk_C))
% 1.37/1.61        | ~ (v2_funct_1 @ sk_C)
% 1.37/1.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61            != (k2_relat_1 @ sk_C)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['119', '120'])).
% 1.37/1.61  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('123', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('124', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('125', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('126', plain,
% 1.37/1.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.61      inference('sup+', [status(thm)], ['124', '125'])).
% 1.37/1.61  thf('127', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('128', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.37/1.61      inference('demod', [status(thm)], ['126', '127'])).
% 1.37/1.61  thf('129', plain,
% 1.37/1.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['123', '128'])).
% 1.37/1.61  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('131', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('demod', [status(thm)], ['129', '130'])).
% 1.37/1.61  thf('132', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('133', plain,
% 1.37/1.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['131', '132'])).
% 1.37/1.61  thf('134', plain, ((v2_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('135', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('136', plain,
% 1.37/1.61      (![X25 : $i]:
% 1.37/1.61         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.37/1.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.37/1.61  thf('137', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('138', plain,
% 1.37/1.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61          = (k2_struct_0 @ sk_B))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_A))),
% 1.37/1.61      inference('sup+', [status(thm)], ['136', '137'])).
% 1.37/1.61  thf('139', plain, ((l1_struct_0 @ sk_A)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('140', plain,
% 1.37/1.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('demod', [status(thm)], ['138', '139'])).
% 1.37/1.61  thf('141', plain,
% 1.37/1.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61          = (k2_struct_0 @ sk_B))
% 1.37/1.61        | ~ (l1_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['135', '140'])).
% 1.37/1.61  thf('142', plain, ((l1_struct_0 @ sk_B)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('143', plain,
% 1.37/1.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.37/1.61         = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('demod', [status(thm)], ['141', '142'])).
% 1.37/1.61  thf('144', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('145', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('146', plain,
% 1.37/1.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61         = (k2_relat_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['143', '144', '145'])).
% 1.37/1.61  thf('147', plain,
% 1.37/1.61      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61          = (k2_funct_1 @ sk_C))
% 1.37/1.61        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.37/1.61      inference('demod', [status(thm)], ['121', '122', '133', '134', '146'])).
% 1.37/1.61  thf('148', plain,
% 1.37/1.61      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.37/1.61         = (k2_funct_1 @ sk_C))),
% 1.37/1.61      inference('simplify', [status(thm)], ['147'])).
% 1.37/1.61  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.37/1.61      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.61  thf('150', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('demod', [status(thm)], ['107', '108', '148', '149'])).
% 1.37/1.61  thf('151', plain,
% 1.37/1.61      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('sup-', [status(thm)], ['96', '150'])).
% 1.37/1.61  thf('152', plain,
% 1.37/1.61      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('sup-', [status(thm)], ['77', '151'])).
% 1.37/1.61  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 1.37/1.61      inference('sup-', [status(thm)], ['91', '92'])).
% 1.37/1.61  thf('154', plain,
% 1.37/1.61      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.37/1.61         <= (~
% 1.37/1.61             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61                = (k2_struct_0 @ sk_B))))),
% 1.37/1.61      inference('demod', [status(thm)], ['152', '153'])).
% 1.37/1.61  thf('155', plain,
% 1.37/1.61      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          = (k2_struct_0 @ sk_B)))),
% 1.37/1.61      inference('simplify', [status(thm)], ['154'])).
% 1.37/1.61  thf('156', plain,
% 1.37/1.61      (~
% 1.37/1.61       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          = (k2_struct_0 @ sk_A))) | 
% 1.37/1.61       ~
% 1.37/1.61       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          = (k2_struct_0 @ sk_B)))),
% 1.37/1.61      inference('split', [status(esa)], ['2'])).
% 1.37/1.61  thf('157', plain,
% 1.37/1.61      (~
% 1.37/1.61       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.37/1.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.37/1.61          = (k2_struct_0 @ sk_A)))),
% 1.37/1.61      inference('sat_resolution*', [status(thm)], ['155', '156'])).
% 1.37/1.61  thf('158', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('simpl_trail', [status(thm)], ['76', '157'])).
% 1.37/1.61  thf('159', plain,
% 1.37/1.61      (![X1 : $i]:
% 1.37/1.61         (~ (v2_funct_1 @ X1)
% 1.37/1.61          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 1.37/1.61          | ~ (v1_funct_1 @ X1)
% 1.37/1.61          | ~ (v1_relat_1 @ X1))),
% 1.37/1.61      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.37/1.61  thf('160', plain,
% 1.37/1.61      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.37/1.61        (k1_zfmisc_1 @ 
% 1.37/1.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.37/1.61      inference('demod', [status(thm)], ['85', '86'])).
% 1.37/1.61  thf('161', plain,
% 1.37/1.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.37/1.61         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.37/1.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.37/1.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.37/1.61  thf('162', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.37/1.61      inference('sup-', [status(thm)], ['160', '161'])).
% 1.37/1.61  thf('163', plain,
% 1.37/1.61      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61          (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.37/1.61        | ~ (v1_relat_1 @ sk_C)
% 1.37/1.61        | ~ (v1_funct_1 @ sk_C)
% 1.37/1.61        | ~ (v2_funct_1 @ sk_C))),
% 1.37/1.61      inference('sup+', [status(thm)], ['159', '162'])).
% 1.37/1.61  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 1.37/1.61      inference('sup-', [status(thm)], ['91', '92'])).
% 1.37/1.61  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 1.37/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.61  thf('167', plain,
% 1.37/1.61      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.37/1.61         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.37/1.61      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 1.37/1.61  thf('168', plain,
% 1.37/1.61      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['158', '167'])).
% 1.37/1.61  thf('169', plain,
% 1.37/1.61      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 1.37/1.61      inference('sup-', [status(thm)], ['0', '168'])).
% 1.37/1.61  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 1.37/1.61      inference('sup-', [status(thm)], ['91', '92'])).
% 1.37/1.61  thf('171', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 1.37/1.61      inference('demod', [status(thm)], ['169', '170'])).
% 1.37/1.61  thf('172', plain, ($false), inference('simplify', [status(thm)], ['171'])).
% 1.37/1.61  
% 1.37/1.61  % SZS output end Refutation
% 1.37/1.61  
% 1.37/1.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
