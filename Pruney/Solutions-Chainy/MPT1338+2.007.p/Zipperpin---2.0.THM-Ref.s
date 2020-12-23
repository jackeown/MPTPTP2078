%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iprb76arsx

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:47 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  220 (1721 expanded)
%              Number of leaves         :   47 ( 525 expanded)
%              Depth                    :   28
%              Number of atoms          : 1995 (44941 expanded)
%              Number of equality atoms :  142 (2345 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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

thf('1',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( v1_partfun1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ( v1_partfun1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('11',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','14','17'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('27',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

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

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('43',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','48','49'])).

thf('51',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('53',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','25','26','51','52'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X37 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['50'])).

thf('62',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('64',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('94',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','85','86','96'])).

thf('98',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('100',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('102',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('107',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('108',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('110',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','112'])).

thf('114',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','113'])).

thf('115',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','114'])).

thf('116',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('123',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['121','122'])).

thf('124',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['53','123'])).

thf('125',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('127',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X37 @ X38 @ X39 ) @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('131',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['125','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('134',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('135',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('137',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('138',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('140',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('141',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('143',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('146',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('147',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('148',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('150',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['149','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['148','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['147','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['144','160'])).

thf('162',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('163',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['141','163'])).

thf('165',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','164'])).

thf('166',plain,(
    ( u1_struct_0 @ sk_B )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','165'])).

thf('167',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','166'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    $false ),
    inference(simplify,[status(thm)],['170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iprb76arsx
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.28/1.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.28/1.47  % Solved by: fo/fo7.sh
% 1.28/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.47  % done 933 iterations in 1.019s
% 1.28/1.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.28/1.47  % SZS output start Refutation
% 1.28/1.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.28/1.47  thf(sk_C_type, type, sk_C: $i).
% 1.28/1.47  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.28/1.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.28/1.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.28/1.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.28/1.47  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.28/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.47  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.28/1.47  thf(sk_B_type, type, sk_B: $i).
% 1.28/1.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.28/1.47  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.28/1.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.28/1.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.28/1.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.28/1.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.28/1.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.28/1.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.28/1.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.28/1.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.28/1.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.28/1.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.28/1.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.28/1.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.28/1.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.28/1.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.28/1.47  thf(d3_struct_0, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.28/1.47  thf('0', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf(t62_tops_2, conjecture,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( l1_struct_0 @ A ) =>
% 1.28/1.47       ( ![B:$i]:
% 1.28/1.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.28/1.47           ( ![C:$i]:
% 1.28/1.47             ( ( ( v1_funct_1 @ C ) & 
% 1.28/1.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.28/1.47                 ( m1_subset_1 @
% 1.28/1.47                   C @ 
% 1.28/1.47                   ( k1_zfmisc_1 @
% 1.28/1.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.28/1.47               ( ( ( ( k2_relset_1 @
% 1.28/1.47                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.28/1.47                     ( k2_struct_0 @ B ) ) & 
% 1.28/1.47                   ( v2_funct_1 @ C ) ) =>
% 1.28/1.47                 ( ( ( k1_relset_1 @
% 1.28/1.47                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.47                       ( k2_tops_2 @
% 1.28/1.47                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.47                     ( k2_struct_0 @ B ) ) & 
% 1.28/1.47                   ( ( k2_relset_1 @
% 1.28/1.47                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.47                       ( k2_tops_2 @
% 1.28/1.47                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.47                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.28/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.47    (~( ![A:$i]:
% 1.28/1.47        ( ( l1_struct_0 @ A ) =>
% 1.28/1.47          ( ![B:$i]:
% 1.28/1.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.28/1.47              ( ![C:$i]:
% 1.28/1.47                ( ( ( v1_funct_1 @ C ) & 
% 1.28/1.47                    ( v1_funct_2 @
% 1.28/1.47                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.28/1.47                    ( m1_subset_1 @
% 1.28/1.47                      C @ 
% 1.28/1.47                      ( k1_zfmisc_1 @
% 1.28/1.47                        ( k2_zfmisc_1 @
% 1.28/1.47                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.28/1.47                  ( ( ( ( k2_relset_1 @
% 1.28/1.47                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.28/1.47                        ( k2_struct_0 @ B ) ) & 
% 1.28/1.47                      ( v2_funct_1 @ C ) ) =>
% 1.28/1.47                    ( ( ( k1_relset_1 @
% 1.28/1.47                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.47                          ( k2_tops_2 @
% 1.28/1.47                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.47                        ( k2_struct_0 @ B ) ) & 
% 1.28/1.47                      ( ( k2_relset_1 @
% 1.28/1.47                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.28/1.47                          ( k2_tops_2 @
% 1.28/1.47                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.28/1.47                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.28/1.47    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.28/1.47  thf('1', plain,
% 1.28/1.47      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          != (k2_struct_0 @ sk_B))
% 1.28/1.47        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47            != (k2_struct_0 @ sk_A)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('2', plain,
% 1.28/1.47      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          != (k2_struct_0 @ sk_B)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_B))))),
% 1.28/1.47      inference('split', [status(esa)], ['1'])).
% 1.28/1.47  thf('3', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(t132_funct_2, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( ( v1_funct_1 @ C ) & 
% 1.28/1.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.28/1.47       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.28/1.47           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.28/1.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.28/1.47           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.28/1.47  thf('4', plain,
% 1.28/1.47      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.28/1.47         (((X29) = (k1_xboole_0))
% 1.28/1.47          | ~ (v1_funct_1 @ X30)
% 1.28/1.47          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 1.28/1.47          | (v1_partfun1 @ X30 @ X31)
% 1.28/1.47          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 1.28/1.47          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 1.28/1.47          | ~ (v1_funct_1 @ X30))),
% 1.28/1.47      inference('cnf', [status(esa)], [t132_funct_2])).
% 1.28/1.47  thf('5', plain,
% 1.28/1.47      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.28/1.47         (~ (v1_funct_2 @ X30 @ X31 @ X29)
% 1.28/1.47          | (v1_partfun1 @ X30 @ X31)
% 1.28/1.47          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 1.28/1.47          | ~ (v1_funct_1 @ X30)
% 1.28/1.47          | ((X29) = (k1_xboole_0)))),
% 1.28/1.47      inference('simplify', [status(thm)], ['4'])).
% 1.28/1.47  thf('6', plain,
% 1.28/1.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.28/1.47        | ~ (v1_funct_1 @ sk_C)
% 1.28/1.47        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.28/1.47        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['3', '5'])).
% 1.28/1.47  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('8', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('9', plain,
% 1.28/1.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.28/1.47        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.28/1.47  thf(d4_partfun1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.28/1.47       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.28/1.47  thf('10', plain,
% 1.28/1.47      (![X27 : $i, X28 : $i]:
% 1.28/1.47         (~ (v1_partfun1 @ X28 @ X27)
% 1.28/1.47          | ((k1_relat_1 @ X28) = (X27))
% 1.28/1.47          | ~ (v4_relat_1 @ X28 @ X27)
% 1.28/1.47          | ~ (v1_relat_1 @ X28))),
% 1.28/1.47      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.28/1.47  thf('11', plain,
% 1.28/1.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.28/1.47        | ~ (v1_relat_1 @ sk_C)
% 1.28/1.47        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.28/1.47        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['9', '10'])).
% 1.28/1.47  thf('12', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(cc1_relset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.47       ( v1_relat_1 @ C ) ))).
% 1.28/1.47  thf('13', plain,
% 1.28/1.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.28/1.47         ((v1_relat_1 @ X7)
% 1.28/1.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.28/1.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.28/1.47  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 1.28/1.47      inference('sup-', [status(thm)], ['12', '13'])).
% 1.28/1.47  thf('15', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(cc2_relset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.28/1.47  thf('16', plain,
% 1.28/1.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.28/1.47         ((v4_relat_1 @ X10 @ X11)
% 1.28/1.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.28/1.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.28/1.47  thf('17', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('sup-', [status(thm)], ['15', '16'])).
% 1.28/1.47  thf('18', plain,
% 1.28/1.47      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.28/1.47        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('demod', [status(thm)], ['11', '14', '17'])).
% 1.28/1.47  thf(fc2_struct_0, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.28/1.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.28/1.47  thf('19', plain,
% 1.28/1.47      (![X33 : $i]:
% 1.28/1.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 1.28/1.47          | ~ (l1_struct_0 @ X33)
% 1.28/1.47          | (v2_struct_0 @ X33))),
% 1.28/1.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.28/1.47  thf('20', plain,
% 1.28/1.47      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.28/1.47        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 1.28/1.47        | (v2_struct_0 @ sk_B)
% 1.28/1.47        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup-', [status(thm)], ['18', '19'])).
% 1.28/1.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.28/1.47  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.28/1.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.28/1.47  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('23', plain,
% 1.28/1.47      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.28/1.47  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('25', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('26', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('27', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('28', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('29', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('30', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('demod', [status(thm)], ['28', '29'])).
% 1.28/1.47  thf(d4_tops_2, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.28/1.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.28/1.47       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.28/1.47         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.28/1.47  thf('31', plain,
% 1.28/1.47      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.28/1.47         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 1.28/1.47          | ~ (v2_funct_1 @ X36)
% 1.28/1.47          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 1.28/1.47          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.28/1.47          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.28/1.47          | ~ (v1_funct_1 @ X36))),
% 1.28/1.47      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.28/1.47  thf('32', plain,
% 1.28/1.47      ((~ (v1_funct_1 @ sk_C)
% 1.28/1.47        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.28/1.47        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47            = (k2_funct_1 @ sk_C))
% 1.28/1.47        | ~ (v2_funct_1 @ sk_C)
% 1.28/1.47        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47            != (u1_struct_0 @ sk_B)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['30', '31'])).
% 1.28/1.47  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('34', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('35', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('36', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['34', '35'])).
% 1.28/1.47  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('38', plain,
% 1.28/1.47      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47          = (k2_funct_1 @ sk_C))
% 1.28/1.47        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47            != (u1_struct_0 @ sk_B)))),
% 1.28/1.47      inference('demod', [status(thm)], ['32', '33', '36', '37'])).
% 1.28/1.47  thf('39', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf(redefinition_k2_relset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.28/1.47  thf('40', plain,
% 1.28/1.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.28/1.47         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.28/1.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.28/1.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.28/1.47  thf('41', plain,
% 1.28/1.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('sup-', [status(thm)], ['39', '40'])).
% 1.28/1.47  thf('42', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('43', plain,
% 1.28/1.47      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['41', '42'])).
% 1.28/1.47  thf('44', plain,
% 1.28/1.47      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47          = (k2_funct_1 @ sk_C))
% 1.28/1.47        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.28/1.47      inference('demod', [status(thm)], ['38', '43'])).
% 1.28/1.47  thf('45', plain,
% 1.28/1.47      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.28/1.47        | ~ (l1_struct_0 @ sk_B)
% 1.28/1.47        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47            = (k2_funct_1 @ sk_C)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['27', '44'])).
% 1.28/1.47  thf('46', plain,
% 1.28/1.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('sup-', [status(thm)], ['39', '40'])).
% 1.28/1.47  thf('47', plain,
% 1.28/1.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('48', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('49', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('50', plain,
% 1.28/1.47      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.28/1.47        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47            = (k2_funct_1 @ sk_C)))),
% 1.28/1.47      inference('demod', [status(thm)], ['45', '48', '49'])).
% 1.28/1.47  thf('51', plain,
% 1.28/1.47      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_funct_1 @ sk_C))),
% 1.28/1.47      inference('simplify', [status(thm)], ['50'])).
% 1.28/1.47  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('53', plain,
% 1.28/1.47      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_B))))),
% 1.28/1.47      inference('demod', [status(thm)], ['2', '25', '26', '51', '52'])).
% 1.28/1.47  thf(t55_funct_1, axiom,
% 1.28/1.47    (![A:$i]:
% 1.28/1.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.28/1.47       ( ( v2_funct_1 @ A ) =>
% 1.28/1.47         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.28/1.47           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.28/1.47  thf('54', plain,
% 1.28/1.47      (![X6 : $i]:
% 1.28/1.47         (~ (v2_funct_1 @ X6)
% 1.28/1.47          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 1.28/1.47          | ~ (v1_funct_1 @ X6)
% 1.28/1.47          | ~ (v1_relat_1 @ X6))),
% 1.28/1.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.28/1.47  thf('55', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('demod', [status(thm)], ['28', '29'])).
% 1.28/1.47  thf(dt_k2_tops_2, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.28/1.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.28/1.47       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.28/1.47         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.28/1.47         ( m1_subset_1 @
% 1.28/1.47           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.28/1.47           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.28/1.47  thf('56', plain,
% 1.28/1.47      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.28/1.47         ((m1_subset_1 @ (k2_tops_2 @ X37 @ X38 @ X39) @ 
% 1.28/1.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.28/1.47          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.28/1.47          | ~ (v1_funct_2 @ X39 @ X37 @ X38)
% 1.28/1.47          | ~ (v1_funct_1 @ X39))),
% 1.28/1.47      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.28/1.47  thf('57', plain,
% 1.28/1.47      ((~ (v1_funct_1 @ sk_C)
% 1.28/1.47        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.28/1.47        | (m1_subset_1 @ 
% 1.28/1.47           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.28/1.47           (k1_zfmisc_1 @ 
% 1.28/1.47            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['55', '56'])).
% 1.28/1.47  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('59', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['34', '35'])).
% 1.28/1.47  thf('60', plain,
% 1.28/1.47      ((m1_subset_1 @ 
% 1.28/1.47        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.28/1.47      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.28/1.47  thf('61', plain,
% 1.28/1.47      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_funct_1 @ sk_C))),
% 1.28/1.47      inference('simplify', [status(thm)], ['50'])).
% 1.28/1.47  thf('62', plain,
% 1.28/1.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.28/1.47      inference('demod', [status(thm)], ['60', '61'])).
% 1.28/1.47  thf('63', plain,
% 1.28/1.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.28/1.47         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.28/1.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.28/1.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.28/1.47  thf('64', plain,
% 1.28/1.47      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['62', '63'])).
% 1.28/1.47  thf('65', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('66', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('67', plain,
% 1.28/1.47      (((m1_subset_1 @ sk_C @ 
% 1.28/1.47         (k1_zfmisc_1 @ 
% 1.28/1.47          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.28/1.47        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['65', '66'])).
% 1.28/1.47  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('69', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.28/1.47      inference('demod', [status(thm)], ['67', '68'])).
% 1.28/1.47  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('71', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.28/1.47      inference('demod', [status(thm)], ['69', '70'])).
% 1.28/1.47  thf('72', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('73', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.28/1.47      inference('demod', [status(thm)], ['71', '72'])).
% 1.28/1.47  thf('74', plain,
% 1.28/1.47      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.28/1.47         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 1.28/1.47          | ~ (v2_funct_1 @ X36)
% 1.28/1.47          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 1.28/1.47          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.28/1.47          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.28/1.47          | ~ (v1_funct_1 @ X36))),
% 1.28/1.47      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.28/1.47  thf('75', plain,
% 1.28/1.47      ((~ (v1_funct_1 @ sk_C)
% 1.28/1.47        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.28/1.47        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.47            = (k2_funct_1 @ sk_C))
% 1.28/1.47        | ~ (v2_funct_1 @ sk_C)
% 1.28/1.47        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.47            != (k2_relat_1 @ sk_C)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['73', '74'])).
% 1.28/1.47  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('77', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('78', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('79', plain,
% 1.28/1.47      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.28/1.47        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['77', '78'])).
% 1.28/1.47  thf('80', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('81', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['79', '80'])).
% 1.28/1.47  thf('82', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('83', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['81', '82'])).
% 1.28/1.47  thf('84', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('85', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['83', '84'])).
% 1.28/1.47  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('87', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('88', plain,
% 1.28/1.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('89', plain,
% 1.28/1.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47          = (k2_struct_0 @ sk_B))
% 1.28/1.47        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['87', '88'])).
% 1.28/1.47  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('91', plain,
% 1.28/1.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.28/1.47         = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['89', '90'])).
% 1.28/1.47  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('94', plain,
% 1.28/1.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.47         = (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.28/1.47  thf('95', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('96', plain,
% 1.28/1.47      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.47         = (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['94', '95'])).
% 1.28/1.47  thf('97', plain,
% 1.28/1.47      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.47          = (k2_funct_1 @ sk_C))
% 1.28/1.47        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.28/1.47      inference('demod', [status(thm)], ['75', '76', '85', '86', '96'])).
% 1.28/1.47  thf('98', plain,
% 1.28/1.47      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.47         = (k2_funct_1 @ sk_C))),
% 1.28/1.47      inference('simplify', [status(thm)], ['97'])).
% 1.28/1.47  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('100', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('101', plain,
% 1.28/1.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          != (k2_struct_0 @ sk_A)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('split', [status(esa)], ['1'])).
% 1.28/1.47  thf('102', plain,
% 1.28/1.47      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47           != (k2_struct_0 @ sk_A))
% 1.28/1.47         | ~ (l1_struct_0 @ sk_B)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['100', '101'])).
% 1.28/1.47  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('104', plain,
% 1.28/1.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          != (k2_struct_0 @ sk_A)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('demod', [status(thm)], ['102', '103'])).
% 1.28/1.47  thf('105', plain,
% 1.28/1.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.28/1.47          != (k2_struct_0 @ sk_A)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['99', '104'])).
% 1.28/1.47  thf('106', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('107', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('108', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('109', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('110', plain,
% 1.28/1.47      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.28/1.47      inference('sup+', [status(thm)], ['108', '109'])).
% 1.28/1.47  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('112', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.28/1.47      inference('demod', [status(thm)], ['110', '111'])).
% 1.28/1.47  thf('113', plain,
% 1.28/1.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.28/1.47          != (k1_relat_1 @ sk_C)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('demod', [status(thm)], ['105', '106', '107', '112'])).
% 1.28/1.47  thf('114', plain,
% 1.28/1.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['98', '113'])).
% 1.28/1.47  thf('115', plain,
% 1.28/1.47      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['64', '114'])).
% 1.28/1.47  thf('116', plain,
% 1.28/1.47      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.28/1.47         | ~ (v1_relat_1 @ sk_C)
% 1.28/1.47         | ~ (v1_funct_1 @ sk_C)
% 1.28/1.47         | ~ (v2_funct_1 @ sk_C)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['54', '115'])).
% 1.28/1.47  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 1.28/1.47      inference('sup-', [status(thm)], ['12', '13'])).
% 1.28/1.47  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('120', plain,
% 1.28/1.47      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.28/1.47         <= (~
% 1.28/1.47             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47                = (k2_struct_0 @ sk_A))))),
% 1.28/1.47      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 1.28/1.47  thf('121', plain,
% 1.28/1.47      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          = (k2_struct_0 @ sk_A)))),
% 1.28/1.47      inference('simplify', [status(thm)], ['120'])).
% 1.28/1.47  thf('122', plain,
% 1.28/1.47      (~
% 1.28/1.47       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          = (k2_struct_0 @ sk_B))) | 
% 1.28/1.47       ~
% 1.28/1.47       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          = (k2_struct_0 @ sk_A)))),
% 1.28/1.47      inference('split', [status(esa)], ['1'])).
% 1.28/1.47  thf('123', plain,
% 1.28/1.47      (~
% 1.28/1.47       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.28/1.47          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.28/1.47          = (k2_struct_0 @ sk_B)))),
% 1.28/1.47      inference('sat_resolution*', [status(thm)], ['121', '122'])).
% 1.28/1.47  thf('124', plain,
% 1.28/1.47      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('simpl_trail', [status(thm)], ['53', '123'])).
% 1.28/1.47  thf('125', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('126', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.28/1.47      inference('demod', [status(thm)], ['28', '29'])).
% 1.28/1.47  thf('127', plain,
% 1.28/1.47      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.28/1.47         ((v1_funct_2 @ (k2_tops_2 @ X37 @ X38 @ X39) @ X38 @ X37)
% 1.28/1.47          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.28/1.47          | ~ (v1_funct_2 @ X39 @ X37 @ X38)
% 1.28/1.47          | ~ (v1_funct_1 @ X39))),
% 1.28/1.47      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.28/1.47  thf('128', plain,
% 1.28/1.47      ((~ (v1_funct_1 @ sk_C)
% 1.28/1.47        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.28/1.47        | (v1_funct_2 @ 
% 1.28/1.47           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.28/1.47           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['126', '127'])).
% 1.28/1.47  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('130', plain,
% 1.28/1.47      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['34', '35'])).
% 1.28/1.47  thf('131', plain,
% 1.28/1.47      ((v1_funct_2 @ 
% 1.28/1.47        (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 1.28/1.47        (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.28/1.47  thf('132', plain,
% 1.28/1.47      (((v1_funct_2 @ 
% 1.28/1.47         (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 1.28/1.47         (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 1.28/1.47        | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['125', '131'])).
% 1.28/1.47  thf('133', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('134', plain,
% 1.28/1.47      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.28/1.47         = (k2_funct_1 @ sk_C))),
% 1.28/1.47      inference('simplify', [status(thm)], ['97'])).
% 1.28/1.47  thf('135', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('136', plain,
% 1.28/1.47      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.28/1.47        (k1_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 1.28/1.47  thf(d1_funct_2, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.47       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.28/1.47           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.28/1.47             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.28/1.47         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.28/1.47           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.28/1.47             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.28/1.47  thf(zf_stmt_1, axiom,
% 1.28/1.47    (![C:$i,B:$i,A:$i]:
% 1.28/1.47     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.28/1.47       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.28/1.47  thf('137', plain,
% 1.28/1.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.28/1.47         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 1.28/1.47          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 1.28/1.47          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.28/1.47  thf('138', plain,
% 1.28/1.47      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47           (u1_struct_0 @ sk_B))
% 1.28/1.47        | ((u1_struct_0 @ sk_B)
% 1.28/1.47            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47               (k2_funct_1 @ sk_C))))),
% 1.28/1.47      inference('sup-', [status(thm)], ['136', '137'])).
% 1.28/1.47  thf('139', plain,
% 1.28/1.47      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.28/1.47      inference('demod', [status(thm)], ['60', '61'])).
% 1.28/1.47  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.28/1.47  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.28/1.47  thf(zf_stmt_4, axiom,
% 1.28/1.47    (![B:$i,A:$i]:
% 1.28/1.47     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.28/1.47       ( zip_tseitin_0 @ B @ A ) ))).
% 1.28/1.47  thf(zf_stmt_5, axiom,
% 1.28/1.47    (![A:$i,B:$i,C:$i]:
% 1.28/1.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.47       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.28/1.47         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.28/1.47           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.28/1.47             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.28/1.47  thf('140', plain,
% 1.28/1.47      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.28/1.47         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.28/1.47          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.28/1.47          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.28/1.47  thf('141', plain,
% 1.28/1.47      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47         (u1_struct_0 @ sk_B))
% 1.28/1.47        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['139', '140'])).
% 1.28/1.47  thf('142', plain,
% 1.28/1.47      (![X19 : $i, X20 : $i]:
% 1.28/1.47         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.28/1.47  thf('143', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.28/1.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.28/1.47  thf('144', plain,
% 1.28/1.47      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.28/1.47      inference('sup+', [status(thm)], ['142', '143'])).
% 1.28/1.47  thf('145', plain,
% 1.28/1.47      ((m1_subset_1 @ sk_C @ 
% 1.28/1.47        (k1_zfmisc_1 @ 
% 1.28/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.28/1.47      inference('demod', [status(thm)], ['69', '70'])).
% 1.28/1.47  thf(cc3_relset_1, axiom,
% 1.28/1.47    (![A:$i,B:$i]:
% 1.28/1.47     ( ( v1_xboole_0 @ A ) =>
% 1.28/1.47       ( ![C:$i]:
% 1.28/1.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.28/1.47           ( v1_xboole_0 @ C ) ) ) ))).
% 1.28/1.47  thf('146', plain,
% 1.28/1.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.28/1.47         (~ (v1_xboole_0 @ X13)
% 1.28/1.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X15)))
% 1.28/1.47          | (v1_xboole_0 @ X14))),
% 1.28/1.47      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.28/1.47  thf('147', plain,
% 1.28/1.47      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.28/1.47      inference('sup-', [status(thm)], ['145', '146'])).
% 1.28/1.47  thf(fc11_relat_1, axiom,
% 1.28/1.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 1.28/1.47  thf('148', plain,
% 1.28/1.47      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 1.28/1.47      inference('cnf', [status(esa)], [fc11_relat_1])).
% 1.28/1.47  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('150', plain,
% 1.28/1.47      (![X32 : $i]:
% 1.28/1.47         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.28/1.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.28/1.47  thf('151', plain,
% 1.28/1.47      (![X33 : $i]:
% 1.28/1.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 1.28/1.47          | ~ (l1_struct_0 @ X33)
% 1.28/1.47          | (v2_struct_0 @ X33))),
% 1.28/1.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.28/1.47  thf('152', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.28/1.47          | ~ (l1_struct_0 @ X0)
% 1.28/1.47          | (v2_struct_0 @ X0)
% 1.28/1.47          | ~ (l1_struct_0 @ X0))),
% 1.28/1.47      inference('sup-', [status(thm)], ['150', '151'])).
% 1.28/1.47  thf('153', plain,
% 1.28/1.47      (![X0 : $i]:
% 1.28/1.47         ((v2_struct_0 @ X0)
% 1.28/1.47          | ~ (l1_struct_0 @ X0)
% 1.28/1.47          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.28/1.47      inference('simplify', [status(thm)], ['152'])).
% 1.28/1.47  thf('154', plain,
% 1.28/1.47      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.28/1.47        | ~ (l1_struct_0 @ sk_B)
% 1.28/1.47        | (v2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup-', [status(thm)], ['149', '153'])).
% 1.28/1.47  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('156', plain,
% 1.28/1.47      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['154', '155'])).
% 1.28/1.47  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('158', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('clc', [status(thm)], ['156', '157'])).
% 1.28/1.47  thf('159', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.28/1.47      inference('sup-', [status(thm)], ['148', '158'])).
% 1.28/1.47  thf('160', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['147', '159'])).
% 1.28/1.47  thf('161', plain, (![X0 : $i]: (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0)),
% 1.28/1.47      inference('sup-', [status(thm)], ['144', '160'])).
% 1.28/1.47  thf('162', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.28/1.47      inference('clc', [status(thm)], ['23', '24'])).
% 1.28/1.47  thf('163', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 1.28/1.47      inference('demod', [status(thm)], ['161', '162'])).
% 1.28/1.47  thf('164', plain,
% 1.28/1.47      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47        (u1_struct_0 @ sk_B))),
% 1.28/1.47      inference('demod', [status(thm)], ['141', '163'])).
% 1.28/1.47  thf('165', plain,
% 1.28/1.47      (((u1_struct_0 @ sk_B)
% 1.28/1.47         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.28/1.47            (k2_funct_1 @ sk_C)))),
% 1.28/1.47      inference('demod', [status(thm)], ['138', '164'])).
% 1.28/1.47  thf('166', plain, (((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['124', '165'])).
% 1.28/1.47  thf('167', plain,
% 1.28/1.47      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup-', [status(thm)], ['0', '166'])).
% 1.28/1.47  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.28/1.47      inference('sup+', [status(thm)], ['46', '47'])).
% 1.28/1.47  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 1.28/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.47  thf('170', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 1.28/1.47      inference('demod', [status(thm)], ['167', '168', '169'])).
% 1.28/1.47  thf('171', plain, ($false), inference('simplify', [status(thm)], ['170'])).
% 1.28/1.47  
% 1.28/1.47  % SZS output end Refutation
% 1.28/1.47  
% 1.28/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
