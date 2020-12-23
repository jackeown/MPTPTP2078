%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X321oR2NTK

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:10 EST 2020

% Result     : Theorem 4.55s
% Output     : Refutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  310 (3359 expanded)
%              Number of leaves         :   44 (1012 expanded)
%              Depth                    :   37
%              Number of atoms          : 2876 (72415 expanded)
%              Number of equality atoms :  156 (2586 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
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
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

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
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('38',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
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

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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
    inference('sup+',[status(thm)],['32','33'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('67',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('74',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','58','59','77'])).

thf('79',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','29','34','35','36','37','79'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

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

thf('83',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
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

thf('92',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('98',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('103',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('112',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('113',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','101','110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('116',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('117',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('119',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('130',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('131',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','128','131','132'])).

thf('134',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['119','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('136',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['100'])).

thf('142',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('144',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','150'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('153',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141','155'])).

thf('157',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('158',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('159',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['118','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('163',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['161','164','165','166'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['117','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('175',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('177',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('179',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('180',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('181',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['100'])).

thf('183',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['154'])).

thf('184',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('186',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('199',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['176','199'])).

thf('201',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('202',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('205',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('206',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('208',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('211',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('212',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['203','212'])).

thf('214',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('215',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('216',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['214','218'])).

thf('220',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['213','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['200','224','225','226','227'])).

thf('229',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['175','228'])).

thf('230',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['116','229'])).

thf('231',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('232',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('233',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['100'])).

thf('235',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['230','233','234'])).

thf('236',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['115','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','240'])).

thf('242',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['81','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['243','244','245','246'])).

thf('248',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['80','247'])).

thf('249',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','248'])).

thf('250',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('251',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('252',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_funct_2 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['250','256'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('260',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['257','258','259'])).

thf('261',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    $false ),
    inference(demod,[status(thm)],['249','260','261','262','263'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X321oR2NTK
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.55/4.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.55/4.78  % Solved by: fo/fo7.sh
% 4.55/4.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.55/4.78  % done 1143 iterations in 4.324s
% 4.55/4.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.55/4.78  % SZS output start Refutation
% 4.55/4.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.55/4.78  thf(sk_C_type, type, sk_C: $i).
% 4.55/4.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.55/4.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.55/4.78  thf(sk_B_type, type, sk_B: $i).
% 4.55/4.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.55/4.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.55/4.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.55/4.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.55/4.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.55/4.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.55/4.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.55/4.78  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 4.55/4.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.55/4.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.55/4.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.55/4.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.55/4.78  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 4.55/4.78  thf(sk_A_type, type, sk_A: $i).
% 4.55/4.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.55/4.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.55/4.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.55/4.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.55/4.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.55/4.78  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.55/4.78  thf(t65_funct_1, axiom,
% 4.55/4.78    (![A:$i]:
% 4.55/4.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.55/4.78       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 4.55/4.78  thf('0', plain,
% 4.55/4.78      (![X2 : $i]:
% 4.55/4.78         (~ (v2_funct_1 @ X2)
% 4.55/4.78          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 4.55/4.78          | ~ (v1_funct_1 @ X2)
% 4.55/4.78          | ~ (v1_relat_1 @ X2))),
% 4.55/4.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 4.55/4.78  thf(d3_struct_0, axiom,
% 4.55/4.78    (![A:$i]:
% 4.55/4.78     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.55/4.78  thf('1', plain,
% 4.55/4.78      (![X27 : $i]:
% 4.55/4.78         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.78  thf('2', plain,
% 4.55/4.78      (![X27 : $i]:
% 4.55/4.78         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.78      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.78  thf(t64_tops_2, conjecture,
% 4.55/4.78    (![A:$i]:
% 4.55/4.78     ( ( l1_struct_0 @ A ) =>
% 4.55/4.78       ( ![B:$i]:
% 4.55/4.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.55/4.78           ( ![C:$i]:
% 4.55/4.78             ( ( ( v1_funct_1 @ C ) & 
% 4.55/4.78                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.55/4.78                 ( m1_subset_1 @
% 4.55/4.78                   C @ 
% 4.55/4.78                   ( k1_zfmisc_1 @
% 4.55/4.78                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.55/4.78               ( ( ( ( k2_relset_1 @
% 4.55/4.78                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.55/4.78                     ( k2_struct_0 @ B ) ) & 
% 4.55/4.78                   ( v2_funct_1 @ C ) ) =>
% 4.55/4.78                 ( r2_funct_2 @
% 4.55/4.78                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 4.55/4.78                   ( k2_tops_2 @
% 4.55/4.78                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.55/4.78                     ( k2_tops_2 @
% 4.55/4.78                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 4.55/4.78                   C ) ) ) ) ) ) ))).
% 4.55/4.78  thf(zf_stmt_0, negated_conjecture,
% 4.55/4.78    (~( ![A:$i]:
% 4.55/4.78        ( ( l1_struct_0 @ A ) =>
% 4.55/4.78          ( ![B:$i]:
% 4.55/4.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.55/4.78              ( ![C:$i]:
% 4.55/4.78                ( ( ( v1_funct_1 @ C ) & 
% 4.55/4.78                    ( v1_funct_2 @
% 4.55/4.78                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.55/4.78                    ( m1_subset_1 @
% 4.55/4.78                      C @ 
% 4.55/4.78                      ( k1_zfmisc_1 @
% 4.55/4.78                        ( k2_zfmisc_1 @
% 4.55/4.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.55/4.78                  ( ( ( ( k2_relset_1 @
% 4.55/4.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.55/4.78                        ( k2_struct_0 @ B ) ) & 
% 4.55/4.78                      ( v2_funct_1 @ C ) ) =>
% 4.55/4.78                    ( r2_funct_2 @
% 4.55/4.78                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 4.55/4.78                      ( k2_tops_2 @
% 4.55/4.78                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.55/4.78                        ( k2_tops_2 @
% 4.55/4.78                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 4.55/4.78                      C ) ) ) ) ) ) ) )),
% 4.55/4.78    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 4.55/4.78  thf('3', plain,
% 4.55/4.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.78          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.55/4.78          sk_C)),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf('4', plain,
% 4.55/4.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.78           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.55/4.78           sk_C)
% 4.55/4.78        | ~ (l1_struct_0 @ sk_B))),
% 4.55/4.78      inference('sup-', [status(thm)], ['2', '3'])).
% 4.55/4.78  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf('6', plain,
% 4.55/4.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.78          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 4.55/4.78          sk_C)),
% 4.55/4.78      inference('demod', [status(thm)], ['4', '5'])).
% 4.55/4.78  thf('7', plain,
% 4.55/4.78      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.78           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.78            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 4.55/4.78           sk_C)
% 4.55/4.78        | ~ (l1_struct_0 @ sk_B))),
% 4.55/4.78      inference('sup-', [status(thm)], ['1', '6'])).
% 4.55/4.78  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.78  thf('9', plain,
% 4.55/4.78      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.78          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.55/4.78           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 4.55/4.78          sk_C)),
% 4.55/4.78      inference('demod', [status(thm)], ['7', '8'])).
% 4.55/4.78  thf(d1_funct_2, axiom,
% 4.55/4.78    (![A:$i,B:$i,C:$i]:
% 4.55/4.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.55/4.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.55/4.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.55/4.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.55/4.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.55/4.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.55/4.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.55/4.78  thf(zf_stmt_1, axiom,
% 4.55/4.78    (![B:$i,A:$i]:
% 4.55/4.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.55/4.78       ( zip_tseitin_0 @ B @ A ) ))).
% 4.55/4.78  thf('10', plain,
% 4.55/4.78      (![X12 : $i, X13 : $i]:
% 4.55/4.78         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 4.55/4.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.55/4.78  thf('11', plain,
% 4.55/4.78      ((m1_subset_1 @ sk_C @ 
% 4.55/4.78        (k1_zfmisc_1 @ 
% 4.55/4.78         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.55/4.79  thf(zf_stmt_3, axiom,
% 4.55/4.79    (![C:$i,B:$i,A:$i]:
% 4.55/4.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.55/4.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.55/4.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.55/4.79  thf(zf_stmt_5, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.55/4.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.55/4.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.55/4.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.55/4.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.55/4.79  thf('12', plain,
% 4.55/4.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.55/4.79         (~ (zip_tseitin_0 @ X17 @ X18)
% 4.55/4.79          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 4.55/4.79          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.55/4.79  thf('13', plain,
% 4.55/4.79      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.55/4.79        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['11', '12'])).
% 4.55/4.79  thf('14', plain,
% 4.55/4.79      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 4.55/4.79        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['10', '13'])).
% 4.55/4.79  thf('15', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('16', plain,
% 4.55/4.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.55/4.79         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 4.55/4.79          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 4.55/4.79          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.55/4.79  thf('17', plain,
% 4.55/4.79      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.55/4.79        | ((u1_struct_0 @ sk_A)
% 4.55/4.79            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['15', '16'])).
% 4.55/4.79  thf('18', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(redefinition_k1_relset_1, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.55/4.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.55/4.79  thf('19', plain,
% 4.55/4.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.55/4.79         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 4.55/4.79          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.55/4.79  thf('20', plain,
% 4.55/4.79      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79         = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['18', '19'])).
% 4.55/4.79  thf('21', plain,
% 4.55/4.79      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.55/4.79        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['17', '20'])).
% 4.55/4.79  thf('22', plain,
% 4.55/4.79      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 4.55/4.79        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['14', '21'])).
% 4.55/4.79  thf(fc2_struct_0, axiom,
% 4.55/4.79    (![A:$i]:
% 4.55/4.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.55/4.79       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.55/4.79  thf('23', plain,
% 4.55/4.79      (![X28 : $i]:
% 4.55/4.79         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 4.55/4.79          | ~ (l1_struct_0 @ X28)
% 4.55/4.79          | (v2_struct_0 @ X28))),
% 4.55/4.79      inference('cnf', [status(esa)], [fc2_struct_0])).
% 4.55/4.79  thf('24', plain,
% 4.55/4.79      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.55/4.79        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 4.55/4.79        | (v2_struct_0 @ sk_B)
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup-', [status(thm)], ['22', '23'])).
% 4.55/4.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.55/4.79  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.55/4.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.55/4.79  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('27', plain,
% 4.55/4.79      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['24', '25', '26'])).
% 4.55/4.79  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('29', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('30', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(redefinition_k2_relset_1, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.55/4.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.55/4.79  thf('31', plain,
% 4.55/4.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.55/4.79         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.55/4.79          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.55/4.79  thf('32', plain,
% 4.55/4.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['30', '31'])).
% 4.55/4.79  thf('33', plain,
% 4.55/4.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79         = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('35', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('36', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('38', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('39', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('40', plain,
% 4.55/4.79      (((m1_subset_1 @ sk_C @ 
% 4.55/4.79         (k1_zfmisc_1 @ 
% 4.55/4.79          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['38', '39'])).
% 4.55/4.79  thf('41', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('42', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 4.55/4.79      inference('demod', [status(thm)], ['40', '41'])).
% 4.55/4.79  thf('43', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('44', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.55/4.79      inference('demod', [status(thm)], ['42', '43'])).
% 4.55/4.79  thf('45', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('46', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.55/4.79      inference('demod', [status(thm)], ['44', '45'])).
% 4.55/4.79  thf(d4_tops_2, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.55/4.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.55/4.79       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 4.55/4.79         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 4.55/4.79  thf('47', plain,
% 4.55/4.79      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.55/4.79         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 4.55/4.79          | ~ (v2_funct_1 @ X31)
% 4.55/4.79          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 4.55/4.79          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 4.55/4.79          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 4.55/4.79          | ~ (v1_funct_1 @ X31))),
% 4.55/4.79      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.55/4.79  thf('48', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.55/4.79        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79            = (k2_funct_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.55/4.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79            != (k2_relat_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['46', '47'])).
% 4.55/4.79  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('50', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('51', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('52', plain,
% 4.55/4.79      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['50', '51'])).
% 4.55/4.79  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('54', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['52', '53'])).
% 4.55/4.79  thf('55', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('56', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['54', '55'])).
% 4.55/4.79  thf('57', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('58', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['56', '57'])).
% 4.55/4.79  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('60', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('61', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('62', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('63', plain,
% 4.55/4.79      (((m1_subset_1 @ sk_C @ 
% 4.55/4.79         (k1_zfmisc_1 @ 
% 4.55/4.79          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_A))),
% 4.55/4.79      inference('sup+', [status(thm)], ['61', '62'])).
% 4.55/4.79  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('65', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('demod', [status(thm)], ['63', '64'])).
% 4.55/4.79  thf('66', plain,
% 4.55/4.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.55/4.79         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.55/4.79          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.55/4.79  thf('67', plain,
% 4.55/4.79      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['65', '66'])).
% 4.55/4.79  thf('68', plain,
% 4.55/4.79      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79          = (k2_relat_1 @ sk_C))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['60', '67'])).
% 4.55/4.79  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('71', plain,
% 4.55/4.79      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['68', '69', '70'])).
% 4.55/4.79  thf('72', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('73', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('74', plain,
% 4.55/4.79      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 4.55/4.79      inference('sup+', [status(thm)], ['72', '73'])).
% 4.55/4.79  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('76', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['74', '75'])).
% 4.55/4.79  thf('77', plain,
% 4.55/4.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['71', '76'])).
% 4.55/4.79  thf('78', plain,
% 4.55/4.79      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79          = (k2_funct_1 @ sk_C))
% 4.55/4.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['48', '49', '58', '59', '77'])).
% 4.55/4.79  thf('79', plain,
% 4.55/4.79      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79         = (k2_funct_1 @ sk_C))),
% 4.55/4.79      inference('simplify', [status(thm)], ['78'])).
% 4.55/4.79  thf('80', plain,
% 4.55/4.79      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79           (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79          sk_C)),
% 4.55/4.79      inference('demod', [status(thm)],
% 4.55/4.79                ['9', '29', '34', '35', '36', '37', '79'])).
% 4.55/4.79  thf(fc6_funct_1, axiom,
% 4.55/4.79    (![A:$i]:
% 4.55/4.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 4.55/4.79       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.55/4.79         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 4.55/4.79         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.55/4.79  thf('81', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 4.55/4.79          | ~ (v2_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_relat_1 @ X0))),
% 4.55/4.79      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.55/4.79  thf('82', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.55/4.79      inference('demod', [status(thm)], ['44', '45'])).
% 4.55/4.79  thf(t31_funct_2, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.55/4.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.55/4.79       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.55/4.79         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.55/4.79           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.55/4.79           ( m1_subset_1 @
% 4.55/4.79             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.55/4.79  thf('83', plain,
% 4.55/4.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X24)
% 4.55/4.79          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.55/4.79          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 4.55/4.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.55/4.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.55/4.79          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.55/4.79          | ~ (v1_funct_1 @ X24))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.55/4.79  thf('84', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.55/4.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79            != (k2_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['82', '83'])).
% 4.55/4.79  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('86', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['56', '57'])).
% 4.55/4.79  thf('87', plain,
% 4.55/4.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['71', '76'])).
% 4.55/4.79  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('89', plain,
% 4.55/4.79      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79         (k1_zfmisc_1 @ 
% 4.55/4.79          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.55/4.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 4.55/4.79  thf('90', plain,
% 4.55/4.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.55/4.79      inference('simplify', [status(thm)], ['89'])).
% 4.55/4.79  thf('91', plain,
% 4.55/4.79      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.55/4.79         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 4.55/4.79          | ~ (v2_funct_1 @ X31)
% 4.55/4.79          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 4.55/4.79          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 4.55/4.79          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 4.55/4.79          | ~ (v1_funct_1 @ X31))),
% 4.55/4.79      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.55/4.79  thf('92', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.55/4.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.55/4.79             (k1_relat_1 @ sk_C))
% 4.55/4.79        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.55/4.79        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['90', '91'])).
% 4.55/4.79  thf('93', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.55/4.79      inference('demod', [status(thm)], ['44', '45'])).
% 4.55/4.79  thf('94', plain,
% 4.55/4.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X24)
% 4.55/4.79          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.55/4.79          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 4.55/4.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.55/4.79          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.55/4.79          | ~ (v1_funct_1 @ X24))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.55/4.79  thf('95', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.55/4.79        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.55/4.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79            != (k2_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['93', '94'])).
% 4.55/4.79  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('97', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['56', '57'])).
% 4.55/4.79  thf('98', plain,
% 4.55/4.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['71', '76'])).
% 4.55/4.79  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('100', plain,
% 4.55/4.79      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.55/4.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 4.55/4.79  thf('101', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.55/4.79      inference('simplify', [status(thm)], ['100'])).
% 4.55/4.79  thf('102', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.55/4.79      inference('demod', [status(thm)], ['44', '45'])).
% 4.55/4.79  thf('103', plain,
% 4.55/4.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X24)
% 4.55/4.79          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.55/4.79          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 4.55/4.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.55/4.79          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.55/4.79          | ~ (v1_funct_1 @ X24))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.55/4.79  thf('104', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C))
% 4.55/4.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79            != (k2_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['102', '103'])).
% 4.55/4.79  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('106', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['56', '57'])).
% 4.55/4.79  thf('107', plain,
% 4.55/4.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['71', '76'])).
% 4.55/4.79  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('109', plain,
% 4.55/4.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.55/4.79         (k1_relat_1 @ sk_C))
% 4.55/4.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 4.55/4.79  thf('110', plain,
% 4.55/4.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 4.55/4.79        (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('simplify', [status(thm)], ['109'])).
% 4.55/4.79  thf('111', plain,
% 4.55/4.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.55/4.79      inference('simplify', [status(thm)], ['89'])).
% 4.55/4.79  thf('112', plain,
% 4.55/4.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.55/4.79         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.55/4.79          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.55/4.79  thf('113', plain,
% 4.55/4.79      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['111', '112'])).
% 4.55/4.79  thf('114', plain,
% 4.55/4.79      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.55/4.79        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['92', '101', '110', '113'])).
% 4.55/4.79  thf('115', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 4.55/4.79          | ~ (v2_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_relat_1 @ X0))),
% 4.55/4.79      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.55/4.79  thf(t55_funct_1, axiom,
% 4.55/4.79    (![A:$i]:
% 4.55/4.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.55/4.79       ( ( v2_funct_1 @ A ) =>
% 4.55/4.79         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.55/4.79           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.55/4.79  thf('116', plain,
% 4.55/4.79      (![X1 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X1)
% 4.55/4.79          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 4.55/4.79          | ~ (v1_funct_1 @ X1)
% 4.55/4.79          | ~ (v1_relat_1 @ X1))),
% 4.55/4.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.55/4.79  thf('117', plain,
% 4.55/4.79      (![X1 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X1)
% 4.55/4.79          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 4.55/4.79          | ~ (v1_funct_1 @ X1)
% 4.55/4.79          | ~ (v1_relat_1 @ X1))),
% 4.55/4.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.55/4.79  thf('118', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 4.55/4.79          | ~ (v2_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_relat_1 @ X0))),
% 4.55/4.79      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.55/4.79  thf('119', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('120', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('121', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('122', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('demod', [status(thm)], ['120', '121'])).
% 4.55/4.79  thf('123', plain,
% 4.55/4.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X24)
% 4.55/4.79          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.55/4.79          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 4.55/4.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.55/4.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.55/4.79          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.55/4.79          | ~ (v1_funct_1 @ X24))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.55/4.79  thf('124', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.55/4.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79            != (u1_struct_0 @ sk_B))
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['122', '123'])).
% 4.55/4.79  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('126', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('127', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('128', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['126', '127'])).
% 4.55/4.79  thf('129', plain,
% 4.55/4.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['30', '31'])).
% 4.55/4.79  thf('130', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('131', plain,
% 4.55/4.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['129', '130'])).
% 4.55/4.79  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('133', plain,
% 4.55/4.79      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79         (k1_zfmisc_1 @ 
% 4.55/4.79          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.55/4.79        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.55/4.79      inference('demod', [status(thm)], ['124', '125', '128', '131', '132'])).
% 4.55/4.79  thf('134', plain,
% 4.55/4.79      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B)
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.55/4.79      inference('sup-', [status(thm)], ['119', '133'])).
% 4.55/4.79  thf('135', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('136', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('137', plain,
% 4.55/4.79      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.55/4.79      inference('demod', [status(thm)], ['134', '135', '136'])).
% 4.55/4.79  thf('138', plain,
% 4.55/4.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.55/4.79      inference('simplify', [status(thm)], ['137'])).
% 4.55/4.79  thf('139', plain,
% 4.55/4.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X24)
% 4.55/4.79          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.55/4.79          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 4.55/4.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.55/4.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.55/4.79          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.55/4.79          | ~ (v1_funct_1 @ X24))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.55/4.79  thf('140', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.55/4.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79             (k1_relat_1 @ sk_C))
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.55/4.79        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['138', '139'])).
% 4.55/4.79  thf('141', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.55/4.79      inference('simplify', [status(thm)], ['100'])).
% 4.55/4.79  thf('142', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('143', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('demod', [status(thm)], ['120', '121'])).
% 4.55/4.79  thf('144', plain,
% 4.55/4.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X24)
% 4.55/4.79          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.55/4.79          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 4.55/4.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.55/4.79          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.55/4.79          | ~ (v1_funct_1 @ X24))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.55/4.79  thf('145', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C))
% 4.55/4.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79            != (u1_struct_0 @ sk_B))
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C))),
% 4.55/4.79      inference('sup-', [status(thm)], ['143', '144'])).
% 4.55/4.79  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('147', plain,
% 4.55/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.55/4.79      inference('demod', [status(thm)], ['126', '127'])).
% 4.55/4.79  thf('148', plain,
% 4.55/4.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.55/4.79         = (k2_relat_1 @ sk_C))),
% 4.55/4.79      inference('demod', [status(thm)], ['129', '130'])).
% 4.55/4.79  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('150', plain,
% 4.55/4.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79         (k1_relat_1 @ sk_C))
% 4.55/4.79        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.55/4.79      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 4.55/4.79  thf('151', plain,
% 4.55/4.79      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B)
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['142', '150'])).
% 4.55/4.79  thf('152', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('153', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('154', plain,
% 4.55/4.79      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['151', '152', '153'])).
% 4.55/4.79  thf('155', plain,
% 4.55/4.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79        (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('simplify', [status(thm)], ['154'])).
% 4.55/4.79  thf('156', plain,
% 4.55/4.79      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79         (k1_zfmisc_1 @ 
% 4.55/4.79          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.55/4.79        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['140', '141', '155'])).
% 4.55/4.79  thf('157', plain,
% 4.55/4.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.55/4.79      inference('simplify', [status(thm)], ['137'])).
% 4.55/4.79  thf('158', plain,
% 4.55/4.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.55/4.79         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 4.55/4.79          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.55/4.79  thf('159', plain,
% 4.55/4.79      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['157', '158'])).
% 4.55/4.79  thf('160', plain,
% 4.55/4.79      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79         (k1_zfmisc_1 @ 
% 4.55/4.79          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.55/4.79        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['156', '159'])).
% 4.55/4.79  thf('161', plain,
% 4.55/4.79      ((~ (v1_relat_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.55/4.79        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.55/4.79      inference('sup-', [status(thm)], ['118', '160'])).
% 4.55/4.79  thf('162', plain,
% 4.55/4.79      ((m1_subset_1 @ sk_C @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf(cc1_relset_1, axiom,
% 4.55/4.79    (![A:$i,B:$i,C:$i]:
% 4.55/4.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.55/4.79       ( v1_relat_1 @ C ) ))).
% 4.55/4.79  thf('163', plain,
% 4.55/4.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.55/4.79         ((v1_relat_1 @ X3)
% 4.55/4.79          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 4.55/4.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.55/4.79  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 4.55/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.55/4.79  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('167', plain,
% 4.55/4.79      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.55/4.79      inference('demod', [status(thm)], ['161', '164', '165', '166'])).
% 4.55/4.79  thf('168', plain,
% 4.55/4.79      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v1_relat_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.55/4.79      inference('sup-', [status(thm)], ['117', '167'])).
% 4.55/4.79  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 4.55/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.55/4.79  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('172', plain,
% 4.55/4.79      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_zfmisc_1 @ 
% 4.55/4.79            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 4.55/4.79      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 4.55/4.79  thf('173', plain,
% 4.55/4.79      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.55/4.79      inference('simplify', [status(thm)], ['172'])).
% 4.55/4.79  thf('174', plain,
% 4.55/4.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.55/4.79         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 4.55/4.79          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 4.55/4.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.55/4.79  thf('175', plain,
% 4.55/4.79      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.55/4.79         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.55/4.79      inference('sup-', [status(thm)], ['173', '174'])).
% 4.55/4.79  thf('176', plain,
% 4.55/4.79      (![X2 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X2)
% 4.55/4.79          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 4.55/4.79          | ~ (v1_funct_1 @ X2)
% 4.55/4.79          | ~ (v1_relat_1 @ X2))),
% 4.55/4.79      inference('cnf', [status(esa)], [t65_funct_1])).
% 4.55/4.79  thf('177', plain,
% 4.55/4.79      (![X1 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X1)
% 4.55/4.79          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 4.55/4.79          | ~ (v1_funct_1 @ X1)
% 4.55/4.79          | ~ (v1_relat_1 @ X1))),
% 4.55/4.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.55/4.79  thf('178', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 4.55/4.79          | ~ (v2_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_funct_1 @ X0)
% 4.55/4.79          | ~ (v1_relat_1 @ X0))),
% 4.55/4.79      inference('cnf', [status(esa)], [fc6_funct_1])).
% 4.55/4.79  thf('179', plain,
% 4.55/4.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.55/4.79        (k1_zfmisc_1 @ 
% 4.55/4.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.55/4.79      inference('simplify', [status(thm)], ['137'])).
% 4.55/4.79  thf('180', plain,
% 4.55/4.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.55/4.79         (~ (v2_funct_1 @ X24)
% 4.55/4.79          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 4.55/4.79          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 4.55/4.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 4.55/4.79          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 4.55/4.79          | ~ (v1_funct_1 @ X24))),
% 4.55/4.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.55/4.79  thf('181', plain,
% 4.55/4.79      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.55/4.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79             (k1_relat_1 @ sk_C))
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.55/4.79        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['179', '180'])).
% 4.55/4.79  thf('182', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.55/4.79      inference('simplify', [status(thm)], ['100'])).
% 4.55/4.79  thf('183', plain,
% 4.55/4.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79        (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('simplify', [status(thm)], ['154'])).
% 4.55/4.79  thf('184', plain,
% 4.55/4.79      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.55/4.79        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['181', '182', '183'])).
% 4.55/4.79  thf('185', plain,
% 4.55/4.79      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.55/4.79         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['157', '158'])).
% 4.55/4.79  thf('186', plain,
% 4.55/4.79      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.55/4.79        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['184', '185'])).
% 4.55/4.79  thf('187', plain,
% 4.55/4.79      ((~ (v1_relat_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.55/4.79        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['178', '186'])).
% 4.55/4.79  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 4.55/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.55/4.79  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('191', plain,
% 4.55/4.79      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.55/4.79      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 4.55/4.79  thf('192', plain,
% 4.55/4.79      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v1_relat_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['177', '191'])).
% 4.55/4.79  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 4.55/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.55/4.79  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('196', plain,
% 4.55/4.79      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.55/4.79        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.55/4.79      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 4.55/4.79  thf('197', plain,
% 4.55/4.79      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.55/4.79      inference('simplify', [status(thm)], ['196'])).
% 4.55/4.79  thf('198', plain,
% 4.55/4.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.55/4.79         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 4.55/4.79          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 4.55/4.79          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.55/4.79  thf('199', plain,
% 4.55/4.79      ((~ (zip_tseitin_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 4.55/4.79           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 4.55/4.79        | ((k1_relat_1 @ sk_C)
% 4.55/4.79            = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79               (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 4.55/4.79      inference('sup-', [status(thm)], ['197', '198'])).
% 4.55/4.79  thf('200', plain,
% 4.55/4.79      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 4.55/4.79        | ~ (v1_relat_1 @ sk_C)
% 4.55/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.55/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.55/4.79        | ((k1_relat_1 @ sk_C)
% 4.55/4.79            = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.55/4.79               (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 4.55/4.79      inference('sup-', [status(thm)], ['176', '199'])).
% 4.55/4.79  thf('201', plain,
% 4.55/4.79      (![X12 : $i, X13 : $i]:
% 4.55/4.79         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.55/4.79  thf('202', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.55/4.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.55/4.79  thf('203', plain,
% 4.55/4.79      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.55/4.79      inference('sup+', [status(thm)], ['201', '202'])).
% 4.55/4.79  thf('204', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('205', plain,
% 4.55/4.79      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.55/4.79        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['11', '12'])).
% 4.55/4.79  thf('206', plain,
% 4.55/4.79      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B)
% 4.55/4.79        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['204', '205'])).
% 4.55/4.79  thf('207', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('208', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('209', plain,
% 4.55/4.79      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 4.55/4.79        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 4.55/4.79      inference('demod', [status(thm)], ['206', '207', '208'])).
% 4.55/4.79  thf('210', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('211', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.55/4.79      inference('clc', [status(thm)], ['27', '28'])).
% 4.55/4.79  thf('212', plain,
% 4.55/4.79      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 4.55/4.79        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('demod', [status(thm)], ['209', '210', '211'])).
% 4.55/4.79  thf('213', plain,
% 4.55/4.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 4.55/4.79        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 4.55/4.79      inference('sup-', [status(thm)], ['203', '212'])).
% 4.55/4.79  thf('214', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup+', [status(thm)], ['32', '33'])).
% 4.55/4.79  thf('215', plain,
% 4.55/4.79      (![X27 : $i]:
% 4.55/4.79         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 4.55/4.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.55/4.79  thf('216', plain,
% 4.55/4.79      (![X28 : $i]:
% 4.55/4.79         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 4.55/4.79          | ~ (l1_struct_0 @ X28)
% 4.55/4.79          | (v2_struct_0 @ X28))),
% 4.55/4.79      inference('cnf', [status(esa)], [fc2_struct_0])).
% 4.55/4.79  thf('217', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.55/4.79          | ~ (l1_struct_0 @ X0)
% 4.55/4.79          | (v2_struct_0 @ X0)
% 4.55/4.79          | ~ (l1_struct_0 @ X0))),
% 4.55/4.79      inference('sup-', [status(thm)], ['215', '216'])).
% 4.55/4.79  thf('218', plain,
% 4.55/4.79      (![X0 : $i]:
% 4.55/4.79         ((v2_struct_0 @ X0)
% 4.55/4.79          | ~ (l1_struct_0 @ X0)
% 4.55/4.79          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 4.55/4.79      inference('simplify', [status(thm)], ['217'])).
% 4.55/4.79  thf('219', plain,
% 4.55/4.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 4.55/4.79        | ~ (l1_struct_0 @ sk_B)
% 4.55/4.79        | (v2_struct_0 @ sk_B))),
% 4.55/4.79      inference('sup-', [status(thm)], ['214', '218'])).
% 4.55/4.79  thf('220', plain, ((l1_struct_0 @ sk_B)),
% 4.55/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.79  thf('221', plain,
% 4.55/4.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 4.62/4.79      inference('demod', [status(thm)], ['219', '220'])).
% 4.62/4.79  thf('222', plain, (~ (v2_struct_0 @ sk_B)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('223', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 4.62/4.79      inference('clc', [status(thm)], ['221', '222'])).
% 4.62/4.79  thf('224', plain,
% 4.62/4.79      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 4.62/4.79      inference('clc', [status(thm)], ['213', '223'])).
% 4.62/4.79  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 4.62/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.62/4.79  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('228', plain,
% 4.62/4.79      (((k1_relat_1 @ sk_C)
% 4.62/4.79         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.62/4.79            (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.62/4.79      inference('demod', [status(thm)], ['200', '224', '225', '226', '227'])).
% 4.62/4.79  thf('229', plain,
% 4.62/4.79      (((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.62/4.79      inference('sup+', [status(thm)], ['175', '228'])).
% 4.62/4.79  thf('230', plain,
% 4.62/4.79      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.62/4.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.62/4.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.62/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.62/4.79      inference('sup+', [status(thm)], ['116', '229'])).
% 4.62/4.79  thf('231', plain,
% 4.62/4.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.62/4.79        (k1_zfmisc_1 @ 
% 4.62/4.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.62/4.79      inference('simplify', [status(thm)], ['89'])).
% 4.62/4.79  thf('232', plain,
% 4.62/4.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.62/4.79         ((v1_relat_1 @ X3)
% 4.62/4.79          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 4.62/4.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.62/4.79  thf('233', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.62/4.79      inference('sup-', [status(thm)], ['231', '232'])).
% 4.62/4.79  thf('234', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 4.62/4.79      inference('simplify', [status(thm)], ['100'])).
% 4.62/4.79  thf('235', plain,
% 4.62/4.79      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.62/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.62/4.79      inference('demod', [status(thm)], ['230', '233', '234'])).
% 4.62/4.79  thf('236', plain,
% 4.62/4.79      ((~ (v1_relat_1 @ sk_C)
% 4.62/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.62/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.62/4.79        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.62/4.79      inference('sup-', [status(thm)], ['115', '235'])).
% 4.62/4.79  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 4.62/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.62/4.79  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('239', plain, ((v2_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('240', plain,
% 4.62/4.79      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.62/4.79      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 4.62/4.79  thf('241', plain,
% 4.62/4.79      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.62/4.79          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.62/4.79        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.62/4.79        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 4.62/4.79      inference('demod', [status(thm)], ['114', '240'])).
% 4.62/4.79  thf('242', plain,
% 4.62/4.79      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 4.62/4.79        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.62/4.79            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.62/4.79      inference('simplify', [status(thm)], ['241'])).
% 4.62/4.79  thf('243', plain,
% 4.62/4.79      ((~ (v1_relat_1 @ sk_C)
% 4.62/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.62/4.79        | ~ (v2_funct_1 @ sk_C)
% 4.62/4.79        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.62/4.79            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.62/4.79      inference('sup-', [status(thm)], ['81', '242'])).
% 4.62/4.79  thf('244', plain, ((v1_relat_1 @ sk_C)),
% 4.62/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.62/4.79  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('246', plain, ((v2_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('247', plain,
% 4.62/4.79      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.62/4.79         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.62/4.79      inference('demod', [status(thm)], ['243', '244', '245', '246'])).
% 4.62/4.79  thf('248', plain,
% 4.62/4.79      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.62/4.79          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 4.62/4.79      inference('demod', [status(thm)], ['80', '247'])).
% 4.62/4.79  thf('249', plain,
% 4.62/4.79      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.62/4.79           sk_C)
% 4.62/4.79        | ~ (v1_relat_1 @ sk_C)
% 4.62/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.62/4.79        | ~ (v2_funct_1 @ sk_C))),
% 4.62/4.79      inference('sup-', [status(thm)], ['0', '248'])).
% 4.62/4.79  thf('250', plain,
% 4.62/4.79      ((m1_subset_1 @ sk_C @ 
% 4.62/4.79        (k1_zfmisc_1 @ 
% 4.62/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.62/4.79      inference('demod', [status(thm)], ['120', '121'])).
% 4.62/4.79  thf('251', plain,
% 4.62/4.79      ((m1_subset_1 @ sk_C @ 
% 4.62/4.79        (k1_zfmisc_1 @ 
% 4.62/4.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.62/4.79      inference('demod', [status(thm)], ['120', '121'])).
% 4.62/4.79  thf(reflexivity_r2_funct_2, axiom,
% 4.62/4.79    (![A:$i,B:$i,C:$i,D:$i]:
% 4.62/4.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.62/4.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.62/4.79         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.62/4.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.62/4.79       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 4.62/4.79  thf('252', plain,
% 4.62/4.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 4.62/4.79         ((r2_funct_2 @ X20 @ X21 @ X22 @ X22)
% 4.62/4.79          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 4.62/4.79          | ~ (v1_funct_2 @ X22 @ X20 @ X21)
% 4.62/4.79          | ~ (v1_funct_1 @ X22)
% 4.62/4.79          | ~ (v1_funct_1 @ X23)
% 4.62/4.79          | ~ (v1_funct_2 @ X23 @ X20 @ X21)
% 4.62/4.79          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.62/4.79      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 4.62/4.79  thf('253', plain,
% 4.62/4.79      (![X0 : $i]:
% 4.62/4.79         (~ (m1_subset_1 @ X0 @ 
% 4.62/4.79             (k1_zfmisc_1 @ 
% 4.62/4.79              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.62/4.79          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.62/4.79          | ~ (v1_funct_1 @ X0)
% 4.62/4.79          | ~ (v1_funct_1 @ sk_C)
% 4.62/4.79          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.62/4.79          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.62/4.79             sk_C))),
% 4.62/4.79      inference('sup-', [status(thm)], ['251', '252'])).
% 4.62/4.79  thf('254', plain, ((v1_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('255', plain,
% 4.62/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.62/4.79      inference('demod', [status(thm)], ['126', '127'])).
% 4.62/4.79  thf('256', plain,
% 4.62/4.79      (![X0 : $i]:
% 4.62/4.79         (~ (m1_subset_1 @ X0 @ 
% 4.62/4.79             (k1_zfmisc_1 @ 
% 4.62/4.79              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 4.62/4.79          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.62/4.79          | ~ (v1_funct_1 @ X0)
% 4.62/4.79          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.62/4.79             sk_C))),
% 4.62/4.79      inference('demod', [status(thm)], ['253', '254', '255'])).
% 4.62/4.79  thf('257', plain,
% 4.62/4.79      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 4.62/4.79        | ~ (v1_funct_1 @ sk_C)
% 4.62/4.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.62/4.79      inference('sup-', [status(thm)], ['250', '256'])).
% 4.62/4.79  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('259', plain,
% 4.62/4.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.62/4.79      inference('demod', [status(thm)], ['126', '127'])).
% 4.62/4.79  thf('260', plain,
% 4.62/4.79      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 4.62/4.79      inference('demod', [status(thm)], ['257', '258', '259'])).
% 4.62/4.79  thf('261', plain, ((v1_relat_1 @ sk_C)),
% 4.62/4.79      inference('sup-', [status(thm)], ['162', '163'])).
% 4.62/4.79  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('263', plain, ((v2_funct_1 @ sk_C)),
% 4.62/4.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.62/4.79  thf('264', plain, ($false),
% 4.62/4.79      inference('demod', [status(thm)], ['249', '260', '261', '262', '263'])).
% 4.62/4.79  
% 4.62/4.79  % SZS output end Refutation
% 4.62/4.79  
% 4.62/4.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
