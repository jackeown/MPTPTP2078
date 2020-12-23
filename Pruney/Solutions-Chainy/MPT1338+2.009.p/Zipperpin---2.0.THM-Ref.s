%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uarUravlLK

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:47 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  250 (1424 expanded)
%              Number of leaves         :   50 ( 439 expanded)
%              Depth                    :   24
%              Number of atoms          : 2304 (36829 expanded)
%              Number of equality atoms :  174 (1939 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('42',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','36','37','42'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('46',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','47','48'])).

thf('50',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('52',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','25','26','50','51'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k1_relat_1 @ X3 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

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

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('82',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','74','84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('89',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('91',plain,(
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

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('97',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('100',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('103',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('111',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('114',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('116',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','118'])).

thf('120',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','119'])).

thf('121',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','120'])).

thf('122',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('129',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['52','129'])).

thf('131',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('133',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('142',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['143'])).

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

thf('145',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('146',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('149',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('150',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('153',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152','153','154'])).

thf('156',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['147','155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('158',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

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

thf('161',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('162',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('164',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('167',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('169',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('170',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('171',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('172',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','172'])).

thf('174',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('177',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('178',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['176','180'])).

thf('182',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['175','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['168','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['165','187'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('190',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['162','190'])).

thf('192',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','191'])).

thf('193',plain,(
    ( u1_struct_0 @ sk_B )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','192'])).

thf('194',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','193'])).

thf('195',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('196',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    $false ),
    inference(simplify,[status(thm)],['197'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uarUravlLK
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.62/1.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.62/1.80  % Solved by: fo/fo7.sh
% 1.62/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.62/1.80  % done 1393 iterations in 1.338s
% 1.62/1.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.62/1.80  % SZS output start Refutation
% 1.62/1.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.62/1.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.62/1.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.62/1.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.62/1.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.62/1.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.62/1.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.62/1.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.62/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.62/1.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.62/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.62/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.62/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.62/1.80  thf(sk_C_type, type, sk_C: $i).
% 1.62/1.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.62/1.80  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.62/1.80  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.62/1.80  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.62/1.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.62/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.62/1.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.62/1.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.62/1.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.62/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.62/1.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.62/1.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.62/1.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.62/1.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.62/1.80  thf(d3_struct_0, axiom,
% 1.62/1.80    (![A:$i]:
% 1.62/1.80     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.62/1.80  thf('0', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf(t62_tops_2, conjecture,
% 1.62/1.80    (![A:$i]:
% 1.62/1.80     ( ( l1_struct_0 @ A ) =>
% 1.62/1.80       ( ![B:$i]:
% 1.62/1.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.62/1.80           ( ![C:$i]:
% 1.62/1.80             ( ( ( v1_funct_1 @ C ) & 
% 1.62/1.80                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.62/1.80                 ( m1_subset_1 @
% 1.62/1.80                   C @ 
% 1.62/1.80                   ( k1_zfmisc_1 @
% 1.62/1.80                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.62/1.80               ( ( ( ( k2_relset_1 @
% 1.62/1.80                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.62/1.80                     ( k2_struct_0 @ B ) ) & 
% 1.62/1.80                   ( v2_funct_1 @ C ) ) =>
% 1.62/1.80                 ( ( ( k1_relset_1 @
% 1.62/1.80                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.62/1.80                       ( k2_tops_2 @
% 1.62/1.80                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.62/1.80                     ( k2_struct_0 @ B ) ) & 
% 1.62/1.80                   ( ( k2_relset_1 @
% 1.62/1.80                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.62/1.80                       ( k2_tops_2 @
% 1.62/1.80                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.62/1.80                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.62/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.62/1.80    (~( ![A:$i]:
% 1.62/1.80        ( ( l1_struct_0 @ A ) =>
% 1.62/1.80          ( ![B:$i]:
% 1.62/1.80            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.62/1.80              ( ![C:$i]:
% 1.62/1.80                ( ( ( v1_funct_1 @ C ) & 
% 1.62/1.80                    ( v1_funct_2 @
% 1.62/1.80                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.62/1.80                    ( m1_subset_1 @
% 1.62/1.80                      C @ 
% 1.62/1.80                      ( k1_zfmisc_1 @
% 1.62/1.80                        ( k2_zfmisc_1 @
% 1.62/1.80                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.62/1.80                  ( ( ( ( k2_relset_1 @
% 1.62/1.80                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.62/1.80                        ( k2_struct_0 @ B ) ) & 
% 1.62/1.80                      ( v2_funct_1 @ C ) ) =>
% 1.62/1.80                    ( ( ( k1_relset_1 @
% 1.62/1.80                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.62/1.80                          ( k2_tops_2 @
% 1.62/1.80                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.62/1.80                        ( k2_struct_0 @ B ) ) & 
% 1.62/1.80                      ( ( k2_relset_1 @
% 1.62/1.80                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.62/1.80                          ( k2_tops_2 @
% 1.62/1.80                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.62/1.80                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.62/1.80    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.62/1.80  thf('1', plain,
% 1.62/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          != (k2_struct_0 @ sk_B))
% 1.62/1.80        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80            != (k2_struct_0 @ sk_A)))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('2', plain,
% 1.62/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          != (k2_struct_0 @ sk_B)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_B))))),
% 1.62/1.80      inference('split', [status(esa)], ['1'])).
% 1.62/1.80  thf('3', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf(t132_funct_2, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( ( v1_funct_1 @ C ) & 
% 1.62/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.80       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.62/1.80           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.62/1.80           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.62/1.80  thf('4', plain,
% 1.62/1.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.62/1.80         (((X26) = (k1_xboole_0))
% 1.62/1.80          | ~ (v1_funct_1 @ X27)
% 1.62/1.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 1.62/1.80          | (v1_partfun1 @ X27 @ X28)
% 1.62/1.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 1.62/1.80          | ~ (v1_funct_2 @ X27 @ X28 @ X26)
% 1.62/1.80          | ~ (v1_funct_1 @ X27))),
% 1.62/1.80      inference('cnf', [status(esa)], [t132_funct_2])).
% 1.62/1.80  thf('5', plain,
% 1.62/1.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.62/1.80         (~ (v1_funct_2 @ X27 @ X28 @ X26)
% 1.62/1.80          | (v1_partfun1 @ X27 @ X28)
% 1.62/1.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 1.62/1.80          | ~ (v1_funct_1 @ X27)
% 1.62/1.80          | ((X26) = (k1_xboole_0)))),
% 1.62/1.80      inference('simplify', [status(thm)], ['4'])).
% 1.62/1.80  thf('6', plain,
% 1.62/1.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.62/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.62/1.80        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['3', '5'])).
% 1.62/1.80  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('8', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('9', plain,
% 1.62/1.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.62/1.80        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.62/1.80      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.62/1.80  thf(d4_partfun1, axiom,
% 1.62/1.80    (![A:$i,B:$i]:
% 1.62/1.80     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.62/1.80       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.62/1.80  thf('10', plain,
% 1.62/1.80      (![X24 : $i, X25 : $i]:
% 1.62/1.80         (~ (v1_partfun1 @ X25 @ X24)
% 1.62/1.80          | ((k1_relat_1 @ X25) = (X24))
% 1.62/1.80          | ~ (v4_relat_1 @ X25 @ X24)
% 1.62/1.80          | ~ (v1_relat_1 @ X25))),
% 1.62/1.80      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.62/1.80  thf('11', plain,
% 1.62/1.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.62/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.62/1.80        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.62/1.80        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['9', '10'])).
% 1.62/1.80  thf('12', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf(cc1_relset_1, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.80       ( v1_relat_1 @ C ) ))).
% 1.62/1.80  thf('13', plain,
% 1.62/1.80      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.62/1.80         ((v1_relat_1 @ X4)
% 1.62/1.80          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.62/1.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.62/1.80  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.80      inference('sup-', [status(thm)], ['12', '13'])).
% 1.62/1.80  thf('15', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf(cc2_relset_1, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.62/1.80  thf('16', plain,
% 1.62/1.80      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.62/1.80         ((v4_relat_1 @ X7 @ X8)
% 1.62/1.80          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.62/1.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.62/1.80  thf('17', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('sup-', [status(thm)], ['15', '16'])).
% 1.62/1.80  thf('18', plain,
% 1.62/1.80      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.62/1.80        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.62/1.80      inference('demod', [status(thm)], ['11', '14', '17'])).
% 1.62/1.80  thf(fc2_struct_0, axiom,
% 1.62/1.80    (![A:$i]:
% 1.62/1.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.62/1.80       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.62/1.80  thf('19', plain,
% 1.62/1.80      (![X33 : $i]:
% 1.62/1.80         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 1.62/1.80          | ~ (l1_struct_0 @ X33)
% 1.62/1.80          | (v2_struct_0 @ X33))),
% 1.62/1.80      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.62/1.80  thf('20', plain,
% 1.62/1.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.62/1.80        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 1.62/1.80        | (v2_struct_0 @ sk_B)
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup-', [status(thm)], ['18', '19'])).
% 1.62/1.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.62/1.80  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.62/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.62/1.80  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('23', plain,
% 1.62/1.80      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.62/1.80  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('25', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('26', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('27', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('28', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('29', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('30', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('demod', [status(thm)], ['28', '29'])).
% 1.62/1.80  thf(d4_tops_2, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.62/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.80       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.62/1.80         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.62/1.80  thf('31', plain,
% 1.62/1.80      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.62/1.80         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 1.62/1.80          | ~ (v2_funct_1 @ X36)
% 1.62/1.80          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 1.62/1.80          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.62/1.80          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.62/1.80          | ~ (v1_funct_1 @ X36))),
% 1.62/1.80      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.62/1.80  thf('32', plain,
% 1.62/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.62/1.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80            = (k2_funct_1 @ sk_C))
% 1.62/1.80        | ~ (v2_funct_1 @ sk_C)
% 1.62/1.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80            != (u1_struct_0 @ sk_B)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['30', '31'])).
% 1.62/1.80  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('34', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('35', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('36', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['34', '35'])).
% 1.62/1.80  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('38', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf(redefinition_k2_relset_1, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.62/1.80  thf('39', plain,
% 1.62/1.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.62/1.80         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.62/1.80          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.62/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.62/1.80  thf('40', plain,
% 1.62/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('sup-', [status(thm)], ['38', '39'])).
% 1.62/1.80  thf('41', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('42', plain,
% 1.62/1.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['40', '41'])).
% 1.62/1.80  thf('43', plain,
% 1.62/1.80      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80          = (k2_funct_1 @ sk_C))
% 1.62/1.80        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.62/1.80      inference('demod', [status(thm)], ['32', '33', '36', '37', '42'])).
% 1.62/1.80  thf('44', plain,
% 1.62/1.80      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B)
% 1.62/1.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80            = (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['27', '43'])).
% 1.62/1.80  thf('45', plain,
% 1.62/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('sup-', [status(thm)], ['38', '39'])).
% 1.62/1.80  thf('46', plain,
% 1.62/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('49', plain,
% 1.62/1.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.62/1.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80            = (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['44', '47', '48'])).
% 1.62/1.80  thf('50', plain,
% 1.62/1.80      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_funct_1 @ sk_C))),
% 1.62/1.80      inference('simplify', [status(thm)], ['49'])).
% 1.62/1.80  thf('51', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('52', plain,
% 1.62/1.80      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_B))))),
% 1.62/1.80      inference('demod', [status(thm)], ['2', '25', '26', '50', '51'])).
% 1.62/1.80  thf(t55_funct_1, axiom,
% 1.62/1.80    (![A:$i]:
% 1.62/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.62/1.80       ( ( v2_funct_1 @ A ) =>
% 1.62/1.80         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.62/1.80           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.62/1.80  thf('53', plain,
% 1.62/1.80      (![X3 : $i]:
% 1.62/1.80         (~ (v2_funct_1 @ X3)
% 1.62/1.80          | ((k1_relat_1 @ X3) = (k2_relat_1 @ (k2_funct_1 @ X3)))
% 1.62/1.80          | ~ (v1_funct_1 @ X3)
% 1.62/1.80          | ~ (v1_relat_1 @ X3))),
% 1.62/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.62/1.80  thf('54', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('55', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('56', plain,
% 1.62/1.80      (((m1_subset_1 @ sk_C @ 
% 1.62/1.80         (k1_zfmisc_1 @ 
% 1.62/1.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['54', '55'])).
% 1.62/1.80  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('58', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.62/1.80      inference('demod', [status(thm)], ['56', '57'])).
% 1.62/1.80  thf('59', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('60', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.62/1.80      inference('demod', [status(thm)], ['58', '59'])).
% 1.62/1.80  thf('61', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('62', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.62/1.80      inference('demod', [status(thm)], ['60', '61'])).
% 1.62/1.80  thf(t31_funct_2, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.62/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.80       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.62/1.80         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.62/1.80           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.62/1.80           ( m1_subset_1 @
% 1.62/1.80             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.62/1.80  thf('63', plain,
% 1.62/1.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.62/1.80         (~ (v2_funct_1 @ X29)
% 1.62/1.80          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 1.62/1.80          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 1.62/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.62/1.80          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.62/1.80          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 1.62/1.80          | ~ (v1_funct_1 @ X29))),
% 1.62/1.80      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.62/1.80  thf('64', plain,
% 1.62/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.62/1.80        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80           (k1_zfmisc_1 @ 
% 1.62/1.80            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.62/1.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80            != (k2_relat_1 @ sk_C))
% 1.62/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.62/1.80      inference('sup-', [status(thm)], ['62', '63'])).
% 1.62/1.80  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('66', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('67', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('68', plain,
% 1.62/1.80      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['66', '67'])).
% 1.62/1.80  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('70', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['68', '69'])).
% 1.62/1.80  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('72', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['70', '71'])).
% 1.62/1.80  thf('73', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('74', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['72', '73'])).
% 1.62/1.80  thf('75', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('76', plain,
% 1.62/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('77', plain,
% 1.62/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80          = (k2_struct_0 @ sk_B))
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['75', '76'])).
% 1.62/1.80  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('79', plain,
% 1.62/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['77', '78'])).
% 1.62/1.80  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('82', plain,
% 1.62/1.80      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.62/1.80  thf('83', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('84', plain,
% 1.62/1.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['82', '83'])).
% 1.62/1.80  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('86', plain,
% 1.62/1.80      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80         (k1_zfmisc_1 @ 
% 1.62/1.80          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.62/1.80        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['64', '65', '74', '84', '85'])).
% 1.62/1.80  thf('87', plain,
% 1.62/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.62/1.80      inference('simplify', [status(thm)], ['86'])).
% 1.62/1.80  thf('88', plain,
% 1.62/1.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.62/1.80         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.62/1.80          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.62/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.62/1.80  thf('89', plain,
% 1.62/1.80      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['87', '88'])).
% 1.62/1.80  thf('90', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.62/1.80      inference('demod', [status(thm)], ['60', '61'])).
% 1.62/1.80  thf('91', plain,
% 1.62/1.80      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.62/1.80         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 1.62/1.80          | ~ (v2_funct_1 @ X36)
% 1.62/1.80          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 1.62/1.80          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.62/1.80          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.62/1.80          | ~ (v1_funct_1 @ X36))),
% 1.62/1.80      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.62/1.80  thf('92', plain,
% 1.62/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.62/1.80        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80            = (k2_funct_1 @ sk_C))
% 1.62/1.80        | ~ (v2_funct_1 @ sk_C)
% 1.62/1.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80            != (k2_relat_1 @ sk_C)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['90', '91'])).
% 1.62/1.80  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('94', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['72', '73'])).
% 1.62/1.80  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('96', plain,
% 1.62/1.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['82', '83'])).
% 1.62/1.80  thf('97', plain,
% 1.62/1.80      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80          = (k2_funct_1 @ sk_C))
% 1.62/1.80        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 1.62/1.80  thf('98', plain,
% 1.62/1.80      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.62/1.80         = (k2_funct_1 @ sk_C))),
% 1.62/1.80      inference('simplify', [status(thm)], ['97'])).
% 1.62/1.80  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('100', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('101', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('102', plain,
% 1.62/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          != (k2_struct_0 @ sk_A)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('split', [status(esa)], ['1'])).
% 1.62/1.80  thf('103', plain,
% 1.62/1.80      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80           != (k2_struct_0 @ sk_A))
% 1.62/1.80         | ~ (l1_struct_0 @ sk_B)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['101', '102'])).
% 1.62/1.80  thf('104', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('105', plain,
% 1.62/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          != (k2_struct_0 @ sk_A)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('demod', [status(thm)], ['103', '104'])).
% 1.62/1.80  thf('106', plain,
% 1.62/1.80      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80           != (k2_struct_0 @ sk_A))
% 1.62/1.80         | ~ (l1_struct_0 @ sk_B)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['100', '105'])).
% 1.62/1.80  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('108', plain,
% 1.62/1.80      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          != (k2_struct_0 @ sk_A)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('demod', [status(thm)], ['106', '107'])).
% 1.62/1.80  thf('109', plain,
% 1.62/1.80      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.62/1.80          != (k2_struct_0 @ sk_A)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['99', '108'])).
% 1.62/1.80  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('111', plain,
% 1.62/1.80      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.62/1.80          != (k2_struct_0 @ sk_A)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('demod', [status(thm)], ['109', '110'])).
% 1.62/1.80  thf('112', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('113', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('114', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('115', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('116', plain,
% 1.62/1.80      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.62/1.80      inference('sup+', [status(thm)], ['114', '115'])).
% 1.62/1.80  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('118', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.62/1.80      inference('demod', [status(thm)], ['116', '117'])).
% 1.62/1.80  thf('119', plain,
% 1.62/1.80      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.62/1.80          != (k1_relat_1 @ sk_C)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('demod', [status(thm)], ['111', '112', '113', '118'])).
% 1.62/1.80  thf('120', plain,
% 1.62/1.80      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['98', '119'])).
% 1.62/1.80  thf('121', plain,
% 1.62/1.80      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['89', '120'])).
% 1.62/1.80  thf('122', plain,
% 1.62/1.80      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.62/1.80         | ~ (v1_relat_1 @ sk_C)
% 1.62/1.80         | ~ (v1_funct_1 @ sk_C)
% 1.62/1.80         | ~ (v2_funct_1 @ sk_C)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['53', '121'])).
% 1.62/1.80  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 1.62/1.80      inference('sup-', [status(thm)], ['12', '13'])).
% 1.62/1.80  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('126', plain,
% 1.62/1.80      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.62/1.80         <= (~
% 1.62/1.80             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80                = (k2_struct_0 @ sk_A))))),
% 1.62/1.80      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 1.62/1.80  thf('127', plain,
% 1.62/1.80      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          = (k2_struct_0 @ sk_A)))),
% 1.62/1.80      inference('simplify', [status(thm)], ['126'])).
% 1.62/1.80  thf('128', plain,
% 1.62/1.80      (~
% 1.62/1.80       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          = (k2_struct_0 @ sk_B))) | 
% 1.62/1.80       ~
% 1.62/1.80       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          = (k2_struct_0 @ sk_A)))),
% 1.62/1.80      inference('split', [status(esa)], ['1'])).
% 1.62/1.80  thf('129', plain,
% 1.62/1.80      (~
% 1.62/1.80       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.62/1.80          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.62/1.80          = (k2_struct_0 @ sk_B)))),
% 1.62/1.80      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 1.62/1.80  thf('130', plain,
% 1.62/1.80      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('simpl_trail', [status(thm)], ['52', '129'])).
% 1.62/1.80  thf('131', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('132', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('demod', [status(thm)], ['28', '29'])).
% 1.62/1.80  thf('133', plain,
% 1.62/1.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.62/1.80         (~ (v2_funct_1 @ X29)
% 1.62/1.80          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 1.62/1.80          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 1.62/1.80          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.62/1.80          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 1.62/1.80          | ~ (v1_funct_1 @ X29))),
% 1.62/1.80      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.62/1.80  thf('134', plain,
% 1.62/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.62/1.80        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.62/1.80           (k1_relat_1 @ sk_C))
% 1.62/1.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80            != (u1_struct_0 @ sk_B))
% 1.62/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.62/1.80      inference('sup-', [status(thm)], ['132', '133'])).
% 1.62/1.80  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('136', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['34', '35'])).
% 1.62/1.80  thf('137', plain,
% 1.62/1.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['40', '41'])).
% 1.62/1.80  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('139', plain,
% 1.62/1.80      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.62/1.80         (k1_relat_1 @ sk_C))
% 1.62/1.80        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.62/1.80      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 1.62/1.80  thf('140', plain,
% 1.62/1.80      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B)
% 1.62/1.80        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.62/1.80           (k1_relat_1 @ sk_C)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['131', '139'])).
% 1.62/1.80  thf('141', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('142', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('143', plain,
% 1.62/1.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.62/1.80        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.62/1.80           (k1_relat_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['140', '141', '142'])).
% 1.62/1.80  thf('144', plain,
% 1.62/1.80      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.62/1.80        (k1_relat_1 @ sk_C))),
% 1.62/1.80      inference('simplify', [status(thm)], ['143'])).
% 1.62/1.80  thf(d1_funct_2, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.62/1.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.62/1.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.62/1.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.62/1.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.62/1.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.62/1.80  thf(zf_stmt_1, axiom,
% 1.62/1.80    (![C:$i,B:$i,A:$i]:
% 1.62/1.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.62/1.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.62/1.80  thf('145', plain,
% 1.62/1.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.62/1.80         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.62/1.80          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 1.62/1.80          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.62/1.80  thf('146', plain,
% 1.62/1.80      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80           (u1_struct_0 @ sk_B))
% 1.62/1.80        | ((u1_struct_0 @ sk_B)
% 1.62/1.80            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80               (k2_funct_1 @ sk_C))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['144', '145'])).
% 1.62/1.80  thf('147', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('148', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.62/1.80      inference('demod', [status(thm)], ['28', '29'])).
% 1.62/1.80  thf('149', plain,
% 1.62/1.80      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.62/1.80         (~ (v2_funct_1 @ X29)
% 1.62/1.80          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 1.62/1.80          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 1.62/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.62/1.80          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.62/1.80          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 1.62/1.80          | ~ (v1_funct_1 @ X29))),
% 1.62/1.80      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.62/1.80  thf('150', plain,
% 1.62/1.80      ((~ (v1_funct_1 @ sk_C)
% 1.62/1.80        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.62/1.80        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80           (k1_zfmisc_1 @ 
% 1.62/1.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.62/1.80        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80            != (u1_struct_0 @ sk_B))
% 1.62/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.62/1.80      inference('sup-', [status(thm)], ['148', '149'])).
% 1.62/1.80  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('152', plain,
% 1.62/1.80      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['34', '35'])).
% 1.62/1.80  thf('153', plain,
% 1.62/1.80      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.62/1.80         = (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['40', '41'])).
% 1.62/1.80  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('155', plain,
% 1.62/1.80      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80         (k1_zfmisc_1 @ 
% 1.62/1.80          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.62/1.80        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.62/1.80      inference('demod', [status(thm)], ['150', '151', '152', '153', '154'])).
% 1.62/1.80  thf('156', plain,
% 1.62/1.80      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B)
% 1.62/1.80        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80           (k1_zfmisc_1 @ 
% 1.62/1.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.62/1.80      inference('sup-', [status(thm)], ['147', '155'])).
% 1.62/1.80  thf('157', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('158', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('159', plain,
% 1.62/1.80      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.62/1.80        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80           (k1_zfmisc_1 @ 
% 1.62/1.80            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.62/1.80      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.62/1.80  thf('160', plain,
% 1.62/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.62/1.80      inference('simplify', [status(thm)], ['159'])).
% 1.62/1.80  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.62/1.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.62/1.80  thf(zf_stmt_4, axiom,
% 1.62/1.80    (![B:$i,A:$i]:
% 1.62/1.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.62/1.80       ( zip_tseitin_0 @ B @ A ) ))).
% 1.62/1.80  thf(zf_stmt_5, axiom,
% 1.62/1.80    (![A:$i,B:$i,C:$i]:
% 1.62/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.62/1.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.62/1.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.62/1.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.62/1.80  thf('161', plain,
% 1.62/1.80      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.62/1.80         (~ (zip_tseitin_0 @ X21 @ X22)
% 1.62/1.80          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 1.62/1.80          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.62/1.80  thf('162', plain,
% 1.62/1.80      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80         (u1_struct_0 @ sk_B))
% 1.62/1.80        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['160', '161'])).
% 1.62/1.80  thf('163', plain,
% 1.62/1.80      (![X16 : $i, X17 : $i]:
% 1.62/1.80         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.62/1.80  thf('164', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.62/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.62/1.80  thf('165', plain,
% 1.62/1.80      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.62/1.80      inference('sup+', [status(thm)], ['163', '164'])).
% 1.62/1.80  thf('166', plain,
% 1.62/1.80      ((m1_subset_1 @ sk_C @ 
% 1.62/1.80        (k1_zfmisc_1 @ 
% 1.62/1.80         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.62/1.80      inference('demod', [status(thm)], ['58', '59'])).
% 1.62/1.80  thf(cc3_relset_1, axiom,
% 1.62/1.80    (![A:$i,B:$i]:
% 1.62/1.80     ( ( v1_xboole_0 @ A ) =>
% 1.62/1.80       ( ![C:$i]:
% 1.62/1.80         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.80           ( v1_xboole_0 @ C ) ) ) ))).
% 1.62/1.80  thf('167', plain,
% 1.62/1.80      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.62/1.80         (~ (v1_xboole_0 @ X10)
% 1.62/1.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 1.62/1.80          | (v1_xboole_0 @ X11))),
% 1.62/1.80      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.62/1.80  thf('168', plain,
% 1.62/1.80      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.62/1.80      inference('sup-', [status(thm)], ['166', '167'])).
% 1.62/1.80  thf(l13_xboole_0, axiom,
% 1.62/1.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.62/1.80  thf('169', plain,
% 1.62/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.62/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.62/1.80  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.62/1.80  thf('170', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.80      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.62/1.80  thf(t71_relat_1, axiom,
% 1.62/1.80    (![A:$i]:
% 1.62/1.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.62/1.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.62/1.80  thf('171', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 1.62/1.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.62/1.80  thf('172', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.62/1.80      inference('sup+', [status(thm)], ['170', '171'])).
% 1.62/1.80  thf('173', plain,
% 1.62/1.80      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.62/1.80      inference('sup+', [status(thm)], ['169', '172'])).
% 1.62/1.80  thf('174', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.62/1.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.62/1.80  thf('175', plain,
% 1.62/1.80      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.62/1.80      inference('sup+', [status(thm)], ['173', '174'])).
% 1.62/1.80  thf('176', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('177', plain,
% 1.62/1.80      (![X32 : $i]:
% 1.62/1.80         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 1.62/1.80      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.62/1.80  thf('178', plain,
% 1.62/1.80      (![X33 : $i]:
% 1.62/1.80         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 1.62/1.80          | ~ (l1_struct_0 @ X33)
% 1.62/1.80          | (v2_struct_0 @ X33))),
% 1.62/1.80      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.62/1.80  thf('179', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.62/1.80          | ~ (l1_struct_0 @ X0)
% 1.62/1.80          | (v2_struct_0 @ X0)
% 1.62/1.80          | ~ (l1_struct_0 @ X0))),
% 1.62/1.80      inference('sup-', [status(thm)], ['177', '178'])).
% 1.62/1.80  thf('180', plain,
% 1.62/1.80      (![X0 : $i]:
% 1.62/1.80         ((v2_struct_0 @ X0)
% 1.62/1.80          | ~ (l1_struct_0 @ X0)
% 1.62/1.80          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.62/1.80      inference('simplify', [status(thm)], ['179'])).
% 1.62/1.80  thf('181', plain,
% 1.62/1.80      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.62/1.80        | ~ (l1_struct_0 @ sk_B)
% 1.62/1.80        | (v2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup-', [status(thm)], ['176', '180'])).
% 1.62/1.80  thf('182', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('183', plain,
% 1.62/1.80      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['181', '182'])).
% 1.62/1.80  thf('184', plain, (~ (v2_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('185', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('clc', [status(thm)], ['183', '184'])).
% 1.62/1.80  thf('186', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.62/1.80      inference('sup-', [status(thm)], ['175', '185'])).
% 1.62/1.80  thf('187', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['168', '186'])).
% 1.62/1.80  thf('188', plain, (![X0 : $i]: (zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ X0)),
% 1.62/1.80      inference('sup-', [status(thm)], ['165', '187'])).
% 1.62/1.80  thf('189', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.62/1.80      inference('clc', [status(thm)], ['23', '24'])).
% 1.62/1.80  thf('190', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 1.62/1.80      inference('demod', [status(thm)], ['188', '189'])).
% 1.62/1.80  thf('191', plain,
% 1.62/1.80      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80        (u1_struct_0 @ sk_B))),
% 1.62/1.80      inference('demod', [status(thm)], ['162', '190'])).
% 1.62/1.80  thf('192', plain,
% 1.62/1.80      (((u1_struct_0 @ sk_B)
% 1.62/1.80         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.62/1.80            (k2_funct_1 @ sk_C)))),
% 1.62/1.80      inference('demod', [status(thm)], ['146', '191'])).
% 1.62/1.80  thf('193', plain, (((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['130', '192'])).
% 1.62/1.80  thf('194', plain,
% 1.62/1.80      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup-', [status(thm)], ['0', '193'])).
% 1.62/1.80  thf('195', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.62/1.80      inference('sup+', [status(thm)], ['45', '46'])).
% 1.62/1.80  thf('196', plain, ((l1_struct_0 @ sk_B)),
% 1.62/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.80  thf('197', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 1.62/1.80      inference('demod', [status(thm)], ['194', '195', '196'])).
% 1.62/1.80  thf('198', plain, ($false), inference('simplify', [status(thm)], ['197'])).
% 1.62/1.80  
% 1.62/1.80  % SZS output end Refutation
% 1.62/1.80  
% 1.62/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
