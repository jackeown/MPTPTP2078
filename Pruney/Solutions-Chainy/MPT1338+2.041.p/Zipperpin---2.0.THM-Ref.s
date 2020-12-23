%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aWA8M39C0J

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:54 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 636 expanded)
%              Number of leaves         :   44 ( 206 expanded)
%              Depth                    :   22
%              Number of atoms          : 1920 (15716 expanded)
%              Number of equality atoms :  150 ( 889 expanded)
%              Maximal formula depth    :   16 (   6 average)

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

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('20',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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

thf('33',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

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

thf('40',plain,(
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

thf('41',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('58',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42','49','50','58'])).

thf('60',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('62',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('65',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','26','27','32','62','67'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('73',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_relset_1 @ X15 @ X16 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('76',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('79',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['70','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','85','86','87'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('90',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('93',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('101',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['101','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
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

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['115','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['127','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('138',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['113','114','125','126','138'])).

thf('140',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('142',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100','140','141'])).

thf('143',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','142'])).

thf('144',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('146',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('149',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['147','148'])).

thf('150',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['68','149'])).

thf('151',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('152',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('153',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('154',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['151','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['150','159'])).

thf('161',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('163',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    $false ),
    inference(simplify,[status(thm)],['163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aWA8M39C0J
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:59:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.28/1.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.28/1.51  % Solved by: fo/fo7.sh
% 1.28/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.51  % done 484 iterations in 1.055s
% 1.28/1.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.28/1.51  % SZS output start Refutation
% 1.28/1.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.28/1.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.28/1.51  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 1.28/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.28/1.51  thf(sk_C_type, type, sk_C: $i).
% 1.28/1.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.28/1.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.28/1.51  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.28/1.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.28/1.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.28/1.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.28/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.28/1.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.28/1.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.28/1.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.28/1.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.28/1.51  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.28/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.28/1.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.28/1.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.28/1.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.28/1.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.28/1.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.28/1.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.28/1.51  thf(t37_relat_1, axiom,
% 1.28/1.51    (![A:$i]:
% 1.28/1.51     ( ( v1_relat_1 @ A ) =>
% 1.28/1.51       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.28/1.51         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.28/1.51  thf('0', plain,
% 1.28/1.51      (![X0 : $i]:
% 1.28/1.51         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 1.28/1.51          | ~ (v1_relat_1 @ X0))),
% 1.28/1.51      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.28/1.51  thf(d3_struct_0, axiom,
% 1.28/1.51    (![A:$i]:
% 1.28/1.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.28/1.51  thf('1', plain,
% 1.28/1.51      (![X25 : $i]:
% 1.28/1.51         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.51  thf(t62_tops_2, conjecture,
% 1.28/1.51    (![A:$i]:
% 1.28/1.51     ( ( l1_struct_0 @ A ) =>
% 1.28/1.51       ( ![B:$i]:
% 1.28/1.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.28/1.51           ( ![C:$i]:
% 1.28/1.51             ( ( ( v1_funct_1 @ C ) & 
% 1.28/1.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.28/1.51                 ( m1_subset_1 @
% 1.28/1.51                   C @ 
% 1.28/1.51                   ( k1_zfmisc_1 @
% 1.28/1.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.28/1.51               ( ( ( ( k2_relset_1 @
% 1.28/1.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.28/1.51                     ( k2_struct_0 @ B ) ) & 
% 1.28/1.51                   ( v2_funct_1 @ C ) ) =>
% 1.28/1.51                 ( ( ( k1_relset_1 @
% 1.28/1.51                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.51                       ( k2_tops_2 @
% 1.28/1.52                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.52                     ( k2_struct_0 @ B ) ) & 
% 1.28/1.52                   ( ( k2_relset_1 @
% 1.28/1.52                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.52                       ( k2_tops_2 @
% 1.28/1.52                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.52                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.28/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.52    (~( ![A:$i]:
% 1.28/1.52        ( ( l1_struct_0 @ A ) =>
% 1.28/1.52          ( ![B:$i]:
% 1.28/1.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.28/1.52              ( ![C:$i]:
% 1.28/1.52                ( ( ( v1_funct_1 @ C ) & 
% 1.28/1.52                    ( v1_funct_2 @
% 1.28/1.52                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.28/1.52                    ( m1_subset_1 @
% 1.28/1.52                      C @ 
% 1.28/1.52                      ( k1_zfmisc_1 @
% 1.28/1.52                        ( k2_zfmisc_1 @
% 1.28/1.52                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.28/1.52                  ( ( ( ( k2_relset_1 @
% 1.28/1.52                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.28/1.52                        ( k2_struct_0 @ B ) ) & 
% 1.28/1.52                      ( v2_funct_1 @ C ) ) =>
% 1.28/1.52                    ( ( ( k1_relset_1 @
% 1.28/1.52                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.52                          ( k2_tops_2 @
% 1.28/1.52                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.52                        ( k2_struct_0 @ B ) ) & 
% 1.28/1.52                      ( ( k2_relset_1 @
% 1.28/1.52                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.52                          ( k2_tops_2 @
% 1.28/1.52                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.52                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.28/1.52    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.28/1.52  thf('2', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          != (k2_struct_0 @ sk_B))
% 1.28/1.52        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52            != (k2_struct_0 @ sk_A)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('3', plain,
% 1.28/1.52      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          != (k2_struct_0 @ sk_A)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_A))))),
% 1.28/1.52      inference('split', [status(esa)], ['2'])).
% 1.28/1.52  thf('4', plain,
% 1.28/1.52      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52           != (k2_struct_0 @ sk_A))
% 1.28/1.52         | ~ (l1_struct_0 @ sk_B)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_A))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['1', '3'])).
% 1.28/1.52  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('6', plain,
% 1.28/1.52      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          != (k2_struct_0 @ sk_A)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_A))))),
% 1.28/1.52      inference('demod', [status(thm)], ['4', '5'])).
% 1.28/1.52  thf(d1_funct_2, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.28/1.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.28/1.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.28/1.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.28/1.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.28/1.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.28/1.52  thf(zf_stmt_1, axiom,
% 1.28/1.52    (![B:$i,A:$i]:
% 1.28/1.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.28/1.52       ( zip_tseitin_0 @ B @ A ) ))).
% 1.28/1.52  thf('7', plain,
% 1.28/1.52      (![X17 : $i, X18 : $i]:
% 1.28/1.52         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.28/1.52  thf('8', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.28/1.52  thf(zf_stmt_3, axiom,
% 1.28/1.52    (![C:$i,B:$i,A:$i]:
% 1.28/1.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.28/1.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.28/1.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.28/1.52  thf(zf_stmt_5, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.28/1.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.28/1.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.28/1.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.28/1.52  thf('9', plain,
% 1.28/1.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.28/1.52         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.28/1.52          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.28/1.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.52  thf('10', plain,
% 1.28/1.52      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.28/1.52        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['8', '9'])).
% 1.28/1.52  thf('11', plain,
% 1.28/1.52      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.28/1.52        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['7', '10'])).
% 1.28/1.52  thf('12', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('13', plain,
% 1.28/1.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.28/1.52         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.28/1.52          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.28/1.52          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.28/1.52  thf('14', plain,
% 1.28/1.52      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.28/1.52        | ((u1_struct_0 @ sk_A)
% 1.28/1.52            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['12', '13'])).
% 1.28/1.52  thf('15', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(redefinition_k1_relset_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.28/1.52  thf('16', plain,
% 1.28/1.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.28/1.52         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.28/1.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.28/1.52  thf('17', plain,
% 1.28/1.52      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('sup-', [status(thm)], ['15', '16'])).
% 1.28/1.52  thf('18', plain,
% 1.28/1.52      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.28/1.52        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.28/1.52      inference('demod', [status(thm)], ['14', '17'])).
% 1.28/1.52  thf('19', plain,
% 1.28/1.52      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.28/1.52        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['11', '18'])).
% 1.28/1.52  thf(fc2_struct_0, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.28/1.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.28/1.52  thf('20', plain,
% 1.28/1.52      (![X26 : $i]:
% 1.28/1.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 1.28/1.52          | ~ (l1_struct_0 @ X26)
% 1.28/1.52          | (v2_struct_0 @ X26))),
% 1.28/1.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.28/1.52  thf('21', plain,
% 1.28/1.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.28/1.52        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.28/1.52        | (v2_struct_0 @ sk_B)
% 1.28/1.52        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup-', [status(thm)], ['19', '20'])).
% 1.28/1.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.28/1.52  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.28/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.28/1.52  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('24', plain,
% 1.28/1.52      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.28/1.52  thf('25', plain, (~ (v2_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('26', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('clc', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('27', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('clc', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('28', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(redefinition_k2_relset_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.28/1.52  thf('29', plain,
% 1.28/1.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.28/1.52         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.28/1.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.28/1.52  thf('30', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k2_relat_1 @ sk_C))),
% 1.28/1.52      inference('sup-', [status(thm)], ['28', '29'])).
% 1.28/1.52  thf('31', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('33', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('34', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('35', plain,
% 1.28/1.52      (((m1_subset_1 @ sk_C @ 
% 1.28/1.52         (k1_zfmisc_1 @ 
% 1.28/1.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['33', '34'])).
% 1.28/1.52  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('37', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['35', '36'])).
% 1.28/1.52  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('39', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.28/1.52      inference('demod', [status(thm)], ['37', '38'])).
% 1.28/1.52  thf(d4_tops_2, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.28/1.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.28/1.52       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.28/1.52         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.28/1.52  thf('40', plain,
% 1.28/1.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.28/1.52         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.28/1.52          | ~ (v2_funct_1 @ X29)
% 1.28/1.52          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.28/1.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.28/1.52          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.28/1.52          | ~ (v1_funct_1 @ X29))),
% 1.28/1.52      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.28/1.52  thf('41', plain,
% 1.28/1.52      ((~ (v1_funct_1 @ sk_C)
% 1.28/1.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.28/1.52        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52            = (k2_funct_1 @ sk_C))
% 1.28/1.52        | ~ (v2_funct_1 @ sk_C)
% 1.28/1.52        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52            != (k2_relat_1 @ sk_C)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['39', '40'])).
% 1.28/1.52  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('43', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('44', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('45', plain,
% 1.28/1.52      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['43', '44'])).
% 1.28/1.52  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('47', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['45', '46'])).
% 1.28/1.52  thf('48', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('49', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['47', '48'])).
% 1.28/1.52  thf('50', plain, ((v2_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('51', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('52', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('53', plain,
% 1.28/1.52      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52          = (k2_struct_0 @ sk_B))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['51', '52'])).
% 1.28/1.52  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('55', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['53', '54'])).
% 1.28/1.52  thf('56', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('57', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('58', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52         = (k2_relat_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.28/1.52  thf('59', plain,
% 1.28/1.52      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52          = (k2_funct_1 @ sk_C))
% 1.28/1.52        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.28/1.52      inference('demod', [status(thm)], ['41', '42', '49', '50', '58'])).
% 1.28/1.52  thf('60', plain,
% 1.28/1.52      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52         = (k2_funct_1 @ sk_C))),
% 1.28/1.52      inference('simplify', [status(thm)], ['59'])).
% 1.28/1.52  thf('61', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('clc', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('62', plain,
% 1.28/1.52      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52         = (k2_funct_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['60', '61'])).
% 1.28/1.52  thf('63', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('64', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('clc', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('65', plain,
% 1.28/1.52      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.28/1.52      inference('sup+', [status(thm)], ['63', '64'])).
% 1.28/1.52  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('67', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['65', '66'])).
% 1.28/1.52  thf('68', plain,
% 1.28/1.52      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_A))))),
% 1.28/1.52      inference('demod', [status(thm)], ['6', '26', '27', '32', '62', '67'])).
% 1.28/1.52  thf('69', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 1.28/1.52          | ~ (v1_relat_1 @ X0))),
% 1.28/1.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.28/1.52  thf(d9_funct_1, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.28/1.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.28/1.52  thf('70', plain,
% 1.28/1.52      (![X1 : $i]:
% 1.28/1.52         (~ (v2_funct_1 @ X1)
% 1.28/1.52          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 1.28/1.52          | ~ (v1_funct_1 @ X1)
% 1.28/1.52          | ~ (v1_relat_1 @ X1))),
% 1.28/1.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.28/1.52  thf('71', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(dt_k3_relset_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( m1_subset_1 @
% 1.28/1.52         ( k3_relset_1 @ A @ B @ C ) @ 
% 1.28/1.52         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 1.28/1.52  thf('72', plain,
% 1.28/1.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.28/1.52         ((m1_subset_1 @ (k3_relset_1 @ X5 @ X6 @ X7) @ 
% 1.28/1.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 1.28/1.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.28/1.52  thf('73', plain,
% 1.28/1.52      ((m1_subset_1 @ 
% 1.28/1.52        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['71', '72'])).
% 1.28/1.52  thf('74', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(redefinition_k3_relset_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 1.28/1.52  thf('75', plain,
% 1.28/1.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.28/1.52         (((k3_relset_1 @ X15 @ X16 @ X14) = (k4_relat_1 @ X14))
% 1.28/1.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.28/1.52  thf('76', plain,
% 1.28/1.52      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k4_relat_1 @ sk_C))),
% 1.28/1.52      inference('sup-', [status(thm)], ['74', '75'])).
% 1.28/1.52  thf('77', plain,
% 1.28/1.52      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.28/1.52      inference('demod', [status(thm)], ['73', '76'])).
% 1.28/1.52  thf('78', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('clc', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('79', plain,
% 1.28/1.52      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.28/1.52      inference('demod', [status(thm)], ['77', '78'])).
% 1.28/1.52  thf('80', plain,
% 1.28/1.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.28/1.52         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 1.28/1.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.28/1.52  thf('81', plain,
% 1.28/1.52      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['79', '80'])).
% 1.28/1.52  thf('82', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52          (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.28/1.52        | ~ (v1_relat_1 @ sk_C)
% 1.28/1.52        | ~ (v1_funct_1 @ sk_C)
% 1.28/1.52        | ~ (v2_funct_1 @ sk_C))),
% 1.28/1.52      inference('sup+', [status(thm)], ['70', '81'])).
% 1.28/1.52  thf('83', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(cc1_relset_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.52       ( v1_relat_1 @ C ) ))).
% 1.28/1.52  thf('84', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.28/1.52         ((v1_relat_1 @ X2)
% 1.28/1.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.28/1.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.28/1.52  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 1.28/1.52      inference('sup-', [status(thm)], ['83', '84'])).
% 1.28/1.52  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('88', plain,
% 1.28/1.52      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.28/1.52      inference('demod', [status(thm)], ['82', '85', '86', '87'])).
% 1.28/1.52  thf('89', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('clc', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('90', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('91', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('92', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          != (k2_struct_0 @ sk_B)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('split', [status(esa)], ['2'])).
% 1.28/1.52  thf('93', plain,
% 1.28/1.52      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52           != (k2_struct_0 @ sk_B))
% 1.28/1.52         | ~ (l1_struct_0 @ sk_A)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['91', '92'])).
% 1.28/1.52  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('95', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          != (k2_struct_0 @ sk_B)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['93', '94'])).
% 1.28/1.52  thf('96', plain,
% 1.28/1.52      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52           != (k2_struct_0 @ sk_B))
% 1.28/1.52         | ~ (l1_struct_0 @ sk_B)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['90', '95'])).
% 1.28/1.52  thf('97', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('98', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          != (k2_struct_0 @ sk_B)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['96', '97'])).
% 1.28/1.52  thf('99', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          != (k2_struct_0 @ sk_B)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['89', '98'])).
% 1.28/1.52  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('101', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('102', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('103', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('104', plain,
% 1.28/1.52      (((m1_subset_1 @ sk_C @ 
% 1.28/1.52         (k1_zfmisc_1 @ 
% 1.28/1.52          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_A))),
% 1.28/1.52      inference('sup+', [status(thm)], ['102', '103'])).
% 1.28/1.52  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('106', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['104', '105'])).
% 1.28/1.52  thf('107', plain,
% 1.28/1.52      (((m1_subset_1 @ sk_C @ 
% 1.28/1.52         (k1_zfmisc_1 @ 
% 1.28/1.52          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['101', '106'])).
% 1.28/1.52  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('109', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['107', '108'])).
% 1.28/1.52  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('111', plain,
% 1.28/1.52      ((m1_subset_1 @ sk_C @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.28/1.52      inference('demod', [status(thm)], ['109', '110'])).
% 1.28/1.52  thf('112', plain,
% 1.28/1.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.28/1.52         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 1.28/1.52          | ~ (v2_funct_1 @ X29)
% 1.28/1.52          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 1.28/1.52          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 1.28/1.52          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 1.28/1.52          | ~ (v1_funct_1 @ X29))),
% 1.28/1.52      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.28/1.52  thf('113', plain,
% 1.28/1.52      ((~ (v1_funct_1 @ sk_C)
% 1.28/1.52        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.28/1.52        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52            = (k2_funct_1 @ sk_C))
% 1.28/1.52        | ~ (v2_funct_1 @ sk_C)
% 1.28/1.52        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52            != (k2_relat_1 @ sk_C)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['111', '112'])).
% 1.28/1.52  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('115', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('116', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('117', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('118', plain,
% 1.28/1.52      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_A))),
% 1.28/1.52      inference('sup+', [status(thm)], ['116', '117'])).
% 1.28/1.52  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('120', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['118', '119'])).
% 1.28/1.52  thf('121', plain,
% 1.28/1.52      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['115', '120'])).
% 1.28/1.52  thf('122', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('123', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['121', '122'])).
% 1.28/1.52  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('125', plain,
% 1.28/1.52      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['123', '124'])).
% 1.28/1.52  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('127', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('128', plain,
% 1.28/1.52      (![X25 : $i]:
% 1.28/1.52         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 1.28/1.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.52  thf('129', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('130', plain,
% 1.28/1.52      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52          = (k2_struct_0 @ sk_B))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_A))),
% 1.28/1.52      inference('sup+', [status(thm)], ['128', '129'])).
% 1.28/1.52  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('132', plain,
% 1.28/1.52      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['130', '131'])).
% 1.28/1.52  thf('133', plain,
% 1.28/1.52      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52          = (k2_struct_0 @ sk_B))
% 1.28/1.52        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['127', '132'])).
% 1.28/1.52  thf('134', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('135', plain,
% 1.28/1.52      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.28/1.52         = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('demod', [status(thm)], ['133', '134'])).
% 1.28/1.52  thf('136', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('138', plain,
% 1.28/1.52      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52         = (k2_relat_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['135', '136', '137'])).
% 1.28/1.52  thf('139', plain,
% 1.28/1.52      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52          = (k2_funct_1 @ sk_C))
% 1.28/1.52        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.28/1.52      inference('demod', [status(thm)], ['113', '114', '125', '126', '138'])).
% 1.28/1.52  thf('140', plain,
% 1.28/1.52      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.52         = (k2_funct_1 @ sk_C))),
% 1.28/1.52      inference('simplify', [status(thm)], ['139'])).
% 1.28/1.52  thf('141', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '31'])).
% 1.28/1.52  thf('142', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['99', '100', '140', '141'])).
% 1.28/1.52  thf('143', plain,
% 1.28/1.52      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['88', '142'])).
% 1.28/1.52  thf('144', plain,
% 1.28/1.52      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['69', '143'])).
% 1.28/1.52  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 1.28/1.52      inference('sup-', [status(thm)], ['83', '84'])).
% 1.28/1.52  thf('146', plain,
% 1.28/1.52      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.28/1.52         <= (~
% 1.28/1.52             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52                = (k2_struct_0 @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['144', '145'])).
% 1.28/1.52  thf('147', plain,
% 1.28/1.52      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          = (k2_struct_0 @ sk_B)))),
% 1.28/1.52      inference('simplify', [status(thm)], ['146'])).
% 1.28/1.52  thf('148', plain,
% 1.28/1.52      (~
% 1.28/1.52       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          = (k2_struct_0 @ sk_A))) | 
% 1.28/1.52       ~
% 1.28/1.52       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          = (k2_struct_0 @ sk_B)))),
% 1.28/1.52      inference('split', [status(esa)], ['2'])).
% 1.28/1.52  thf('149', plain,
% 1.28/1.52      (~
% 1.28/1.52       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.52          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.52          = (k2_struct_0 @ sk_A)))),
% 1.28/1.52      inference('sat_resolution*', [status(thm)], ['147', '148'])).
% 1.28/1.52  thf('150', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('simpl_trail', [status(thm)], ['68', '149'])).
% 1.28/1.52  thf('151', plain,
% 1.28/1.52      (![X1 : $i]:
% 1.28/1.52         (~ (v2_funct_1 @ X1)
% 1.28/1.52          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 1.28/1.52          | ~ (v1_funct_1 @ X1)
% 1.28/1.52          | ~ (v1_relat_1 @ X1))),
% 1.28/1.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.28/1.52  thf('152', plain,
% 1.28/1.52      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.28/1.52        (k1_zfmisc_1 @ 
% 1.28/1.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.28/1.52      inference('demod', [status(thm)], ['77', '78'])).
% 1.28/1.52  thf('153', plain,
% 1.28/1.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.28/1.52         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.28/1.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.28/1.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.28/1.52  thf('154', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['152', '153'])).
% 1.28/1.52  thf('155', plain,
% 1.28/1.52      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52          (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.28/1.52        | ~ (v1_relat_1 @ sk_C)
% 1.28/1.52        | ~ (v1_funct_1 @ sk_C)
% 1.28/1.52        | ~ (v2_funct_1 @ sk_C))),
% 1.28/1.52      inference('sup+', [status(thm)], ['151', '154'])).
% 1.28/1.52  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 1.28/1.52      inference('sup-', [status(thm)], ['83', '84'])).
% 1.28/1.52  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('159', plain,
% 1.28/1.52      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.52         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.28/1.52      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 1.28/1.52  thf('160', plain,
% 1.28/1.52      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['150', '159'])).
% 1.28/1.52  thf('161', plain,
% 1.28/1.52      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 1.28/1.52      inference('sup-', [status(thm)], ['0', '160'])).
% 1.28/1.52  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 1.28/1.52      inference('sup-', [status(thm)], ['83', '84'])).
% 1.28/1.52  thf('163', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 1.28/1.52      inference('demod', [status(thm)], ['161', '162'])).
% 1.28/1.52  thf('164', plain, ($false), inference('simplify', [status(thm)], ['163'])).
% 1.28/1.52  
% 1.28/1.52  % SZS output end Refutation
% 1.28/1.52  
% 1.28/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
