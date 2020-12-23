%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4S9lY7rOzN

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:11 EST 2020

% Result     : Theorem 5.87s
% Output     : Refutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :  298 (4770 expanded)
%              Number of leaves         :   44 (1400 expanded)
%              Depth                    :   38
%              Number of atoms          : 2768 (104143 expanded)
%              Number of equality atoms :  149 (3554 expanded)
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('43',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('47',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('49',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','45','46','47','48'])).

thf('50',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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

thf('59',plain,(
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

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('79',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('82',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61','70','71','85'])).

thf('87',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['49','87'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('90',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

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

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('101',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96','99','102','103'])).

thf('105',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['90','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
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

thf('111',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('113',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('123',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('128',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('132',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','120','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('137',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('138',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
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

thf('140',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('141',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('143',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('144',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('147',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('148',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('150',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['142','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('153',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['151','154','155','156'])).

thf('158',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['141','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('165',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('167',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('169',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('170',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('171',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('173',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('174',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('176',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('189',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['166','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('192',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('194',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('196',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('199',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('200',plain,
    ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','200'])).

thf('202',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('203',plain,(
    zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['190','203','204','205','206'])).

thf('208',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['165','207'])).

thf('209',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['140','208'])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('211',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('212',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('215',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('216',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216'])).

thf('218',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('220',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('222',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','220','221'])).

thf('223',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['139','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['223','224','225','226'])).

thf('228',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['138','227'])).

thf('229',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','228'])).

thf('230',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','235'])).

thf('237',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','236'])).

thf('238',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('239',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('240',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_funct_2 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['238','244'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('248',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    $false ),
    inference(demod,[status(thm)],['237','248','249','250','251'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4S9lY7rOzN
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 5.87/6.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.87/6.06  % Solved by: fo/fo7.sh
% 5.87/6.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.87/6.06  % done 1259 iterations in 5.598s
% 5.87/6.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.87/6.06  % SZS output start Refutation
% 5.87/6.06  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.87/6.06  thf(sk_C_type, type, sk_C: $i).
% 5.87/6.06  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.87/6.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.87/6.06  thf(sk_B_type, type, sk_B: $i).
% 5.87/6.06  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.87/6.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.87/6.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.87/6.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.87/6.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.87/6.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.87/6.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.87/6.06  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 5.87/6.06  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.87/6.06  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.87/6.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.87/6.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.87/6.06  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 5.87/6.06  thf(sk_A_type, type, sk_A: $i).
% 5.87/6.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.87/6.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.87/6.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.87/6.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.87/6.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.87/6.06  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.87/6.06  thf(t65_funct_1, axiom,
% 5.87/6.06    (![A:$i]:
% 5.87/6.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.87/6.06       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 5.87/6.06  thf('0', plain,
% 5.87/6.06      (![X2 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X2)
% 5.87/6.06          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 5.87/6.06          | ~ (v1_funct_1 @ X2)
% 5.87/6.06          | ~ (v1_relat_1 @ X2))),
% 5.87/6.06      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.87/6.06  thf(d3_struct_0, axiom,
% 5.87/6.06    (![A:$i]:
% 5.87/6.06     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.87/6.06  thf('1', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('2', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf(t64_tops_2, conjecture,
% 5.87/6.06    (![A:$i]:
% 5.87/6.06     ( ( l1_struct_0 @ A ) =>
% 5.87/6.06       ( ![B:$i]:
% 5.87/6.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 5.87/6.06           ( ![C:$i]:
% 5.87/6.06             ( ( ( v1_funct_1 @ C ) & 
% 5.87/6.06                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.87/6.06                 ( m1_subset_1 @
% 5.87/6.06                   C @ 
% 5.87/6.06                   ( k1_zfmisc_1 @
% 5.87/6.06                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.87/6.06               ( ( ( ( k2_relset_1 @
% 5.87/6.06                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 5.87/6.06                     ( k2_struct_0 @ B ) ) & 
% 5.87/6.06                   ( v2_funct_1 @ C ) ) =>
% 5.87/6.06                 ( r2_funct_2 @
% 5.87/6.06                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 5.87/6.06                   ( k2_tops_2 @
% 5.87/6.06                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.87/6.06                     ( k2_tops_2 @
% 5.87/6.06                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 5.87/6.06                   C ) ) ) ) ) ) ))).
% 5.87/6.06  thf(zf_stmt_0, negated_conjecture,
% 5.87/6.06    (~( ![A:$i]:
% 5.87/6.06        ( ( l1_struct_0 @ A ) =>
% 5.87/6.06          ( ![B:$i]:
% 5.87/6.06            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 5.87/6.06              ( ![C:$i]:
% 5.87/6.06                ( ( ( v1_funct_1 @ C ) & 
% 5.87/6.06                    ( v1_funct_2 @
% 5.87/6.06                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.87/6.06                    ( m1_subset_1 @
% 5.87/6.06                      C @ 
% 5.87/6.06                      ( k1_zfmisc_1 @
% 5.87/6.06                        ( k2_zfmisc_1 @
% 5.87/6.06                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.87/6.06                  ( ( ( ( k2_relset_1 @
% 5.87/6.06                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 5.87/6.06                        ( k2_struct_0 @ B ) ) & 
% 5.87/6.06                      ( v2_funct_1 @ C ) ) =>
% 5.87/6.06                    ( r2_funct_2 @
% 5.87/6.06                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 5.87/6.06                      ( k2_tops_2 @
% 5.87/6.06                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 5.87/6.06                        ( k2_tops_2 @
% 5.87/6.06                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 5.87/6.06                      C ) ) ) ) ) ) ) )),
% 5.87/6.06    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 5.87/6.06  thf('3', plain,
% 5.87/6.06      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.87/6.06           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.87/6.06          sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('4', plain,
% 5.87/6.06      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.87/6.06            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.87/6.06           sk_C)
% 5.87/6.06        | ~ (l1_struct_0 @ sk_A))),
% 5.87/6.06      inference('sup-', [status(thm)], ['2', '3'])).
% 5.87/6.06  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('6', plain,
% 5.87/6.06      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.87/6.06           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 5.87/6.06          sk_C)),
% 5.87/6.06      inference('demod', [status(thm)], ['4', '5'])).
% 5.87/6.06  thf('7', plain,
% 5.87/6.06      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.87/6.06            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 5.87/6.06           sk_C)
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup-', [status(thm)], ['1', '6'])).
% 5.87/6.06  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('9', plain,
% 5.87/6.06      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 5.87/6.06           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 5.87/6.06          sk_C)),
% 5.87/6.06      inference('demod', [status(thm)], ['7', '8'])).
% 5.87/6.06  thf('10', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('11', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf(d1_funct_2, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i]:
% 5.87/6.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.87/6.06       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.87/6.06           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.87/6.06             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.87/6.06         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.87/6.06           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.87/6.06             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.87/6.06  thf(zf_stmt_1, axiom,
% 5.87/6.06    (![B:$i,A:$i]:
% 5.87/6.06     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.87/6.06       ( zip_tseitin_0 @ B @ A ) ))).
% 5.87/6.06  thf('12', plain,
% 5.87/6.06      (![X12 : $i, X13 : $i]:
% 5.87/6.06         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.87/6.06  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.87/6.06  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.87/6.06      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.87/6.06  thf('14', plain,
% 5.87/6.06      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.87/6.06      inference('sup+', [status(thm)], ['12', '13'])).
% 5.87/6.06  thf('15', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.87/6.06  thf(zf_stmt_3, axiom,
% 5.87/6.06    (![C:$i,B:$i,A:$i]:
% 5.87/6.06     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.87/6.06       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.87/6.06  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.87/6.06  thf(zf_stmt_5, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i]:
% 5.87/6.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.87/6.06       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.87/6.06         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.87/6.06           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.87/6.06             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.87/6.06  thf('16', plain,
% 5.87/6.06      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.87/6.06         (~ (zip_tseitin_0 @ X17 @ X18)
% 5.87/6.06          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 5.87/6.06          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.87/6.06  thf('17', plain,
% 5.87/6.06      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.87/6.06        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['15', '16'])).
% 5.87/6.06  thf('18', plain,
% 5.87/6.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 5.87/6.06        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['14', '17'])).
% 5.87/6.06  thf('19', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('20', plain,
% 5.87/6.06      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.87/6.06         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 5.87/6.06          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 5.87/6.06          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.87/6.06  thf('21', plain,
% 5.87/6.06      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.87/6.06        | ((u1_struct_0 @ sk_A)
% 5.87/6.06            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['19', '20'])).
% 5.87/6.06  thf('22', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf(redefinition_k1_relset_1, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i]:
% 5.87/6.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.87/6.06       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.87/6.06  thf('23', plain,
% 5.87/6.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.87/6.06         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 5.87/6.06          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 5.87/6.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.87/6.06  thf('24', plain,
% 5.87/6.06      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06         = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['22', '23'])).
% 5.87/6.06  thf('25', plain,
% 5.87/6.06      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.87/6.06        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['21', '24'])).
% 5.87/6.06  thf('26', plain,
% 5.87/6.06      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 5.87/6.06        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['18', '25'])).
% 5.87/6.06  thf('27', plain,
% 5.87/6.06      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B)
% 5.87/6.06        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('sup+', [status(thm)], ['11', '26'])).
% 5.87/6.06  thf('28', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf(redefinition_k2_relset_1, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i]:
% 5.87/6.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.87/6.06       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.87/6.06  thf('29', plain,
% 5.87/6.06      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.87/6.06         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 5.87/6.06          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 5.87/6.06      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.87/6.06  thf('30', plain,
% 5.87/6.06      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['28', '29'])).
% 5.87/6.06  thf('31', plain,
% 5.87/6.06      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06         = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('34', plain,
% 5.87/6.06      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.87/6.06        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['27', '32', '33'])).
% 5.87/6.06  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf(fc5_struct_0, axiom,
% 5.87/6.06    (![A:$i]:
% 5.87/6.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 5.87/6.06       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 5.87/6.06  thf('36', plain,
% 5.87/6.06      (![X28 : $i]:
% 5.87/6.06         (~ (v1_xboole_0 @ (k2_struct_0 @ X28))
% 5.87/6.06          | ~ (l1_struct_0 @ X28)
% 5.87/6.06          | (v2_struct_0 @ X28))),
% 5.87/6.06      inference('cnf', [status(esa)], [fc5_struct_0])).
% 5.87/6.06  thf('37', plain,
% 5.87/6.06      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.87/6.06        | (v2_struct_0 @ sk_B)
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup-', [status(thm)], ['35', '36'])).
% 5.87/6.06  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('39', plain,
% 5.87/6.06      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 5.87/6.06      inference('demod', [status(thm)], ['37', '38'])).
% 5.87/6.06  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['39', '40'])).
% 5.87/6.06  thf('42', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('43', plain,
% 5.87/6.06      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 5.87/6.06      inference('sup+', [status(thm)], ['10', '42'])).
% 5.87/6.06  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('45', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['43', '44'])).
% 5.87/6.06  thf('46', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('47', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('48', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('49', plain,
% 5.87/6.06      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 5.87/6.06          sk_C)),
% 5.87/6.06      inference('demod', [status(thm)], ['9', '45', '46', '47', '48'])).
% 5.87/6.06  thf('50', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('51', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('52', plain,
% 5.87/6.06      (((m1_subset_1 @ sk_C @ 
% 5.87/6.06         (k1_zfmisc_1 @ 
% 5.87/6.06          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['50', '51'])).
% 5.87/6.06  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('54', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 5.87/6.06      inference('demod', [status(thm)], ['52', '53'])).
% 5.87/6.06  thf('55', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('56', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 5.87/6.06      inference('demod', [status(thm)], ['54', '55'])).
% 5.87/6.06  thf('57', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('58', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.87/6.06      inference('demod', [status(thm)], ['56', '57'])).
% 5.87/6.06  thf(d4_tops_2, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i]:
% 5.87/6.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.87/6.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.87/6.06       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 5.87/6.06         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 5.87/6.06  thf('59', plain,
% 5.87/6.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.87/6.06         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 5.87/6.06          | ~ (v2_funct_1 @ X31)
% 5.87/6.06          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 5.87/6.06          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 5.87/6.06          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 5.87/6.06          | ~ (v1_funct_1 @ X31))),
% 5.87/6.06      inference('cnf', [status(esa)], [d4_tops_2])).
% 5.87/6.06  thf('60', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.87/6.06        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06            = (k2_funct_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06            != (k2_relat_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['58', '59'])).
% 5.87/6.06  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('62', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('63', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('64', plain,
% 5.87/6.06      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['62', '63'])).
% 5.87/6.06  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('66', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('demod', [status(thm)], ['64', '65'])).
% 5.87/6.06  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('68', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['66', '67'])).
% 5.87/6.06  thf('69', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('70', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['68', '69'])).
% 5.87/6.06  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('72', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('73', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('74', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('75', plain,
% 5.87/6.06      (((m1_subset_1 @ sk_C @ 
% 5.87/6.06         (k1_zfmisc_1 @ 
% 5.87/6.06          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_A))),
% 5.87/6.06      inference('sup+', [status(thm)], ['73', '74'])).
% 5.87/6.06  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('77', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('demod', [status(thm)], ['75', '76'])).
% 5.87/6.06  thf('78', plain,
% 5.87/6.06      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.87/6.06         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 5.87/6.06          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 5.87/6.06      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.87/6.06  thf('79', plain,
% 5.87/6.06      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['77', '78'])).
% 5.87/6.06  thf('80', plain,
% 5.87/6.06      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06          = (k2_relat_1 @ sk_C))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['72', '79'])).
% 5.87/6.06  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('83', plain,
% 5.87/6.06      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['80', '81', '82'])).
% 5.87/6.06  thf('84', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['43', '44'])).
% 5.87/6.06  thf('85', plain,
% 5.87/6.06      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['83', '84'])).
% 5.87/6.06  thf('86', plain,
% 5.87/6.06      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06          = (k2_funct_1 @ sk_C))
% 5.87/6.06        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['60', '61', '70', '71', '85'])).
% 5.87/6.06  thf('87', plain,
% 5.87/6.06      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06         = (k2_funct_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['86'])).
% 5.87/6.06  thf('88', plain,
% 5.87/6.06      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06           (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06          sk_C)),
% 5.87/6.06      inference('demod', [status(thm)], ['49', '87'])).
% 5.87/6.06  thf(fc6_funct_1, axiom,
% 5.87/6.06    (![A:$i]:
% 5.87/6.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 5.87/6.06       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.87/6.06         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 5.87/6.06         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.87/6.06  thf('89', plain,
% 5.87/6.06      (![X0 : $i]:
% 5.87/6.06         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.87/6.06          | ~ (v2_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_relat_1 @ X0))),
% 5.87/6.06      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.87/6.06  thf('90', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('91', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('92', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('93', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('demod', [status(thm)], ['91', '92'])).
% 5.87/6.06  thf(t31_funct_2, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i]:
% 5.87/6.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.87/6.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.87/6.06       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.87/6.06         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.87/6.06           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.87/6.06           ( m1_subset_1 @
% 5.87/6.06             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.87/6.06  thf('94', plain,
% 5.87/6.06      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X24)
% 5.87/6.06          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.87/6.06          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 5.87/6.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.87/6.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.87/6.06          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.87/6.06          | ~ (v1_funct_1 @ X24))),
% 5.87/6.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.87/6.06  thf('95', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 5.87/6.06        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06            != (u1_struct_0 @ sk_B))
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['93', '94'])).
% 5.87/6.06  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('97', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('98', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('99', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('demod', [status(thm)], ['97', '98'])).
% 5.87/6.06  thf('100', plain,
% 5.87/6.06      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['28', '29'])).
% 5.87/6.06  thf('101', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('102', plain,
% 5.87/6.06      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['100', '101'])).
% 5.87/6.06  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('104', plain,
% 5.87/6.06      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06         (k1_zfmisc_1 @ 
% 5.87/6.06          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 5.87/6.06        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 5.87/6.06      inference('demod', [status(thm)], ['95', '96', '99', '102', '103'])).
% 5.87/6.06  thf('105', plain,
% 5.87/6.06      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B)
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['90', '104'])).
% 5.87/6.06  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('108', plain,
% 5.87/6.06      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 5.87/6.06      inference('demod', [status(thm)], ['105', '106', '107'])).
% 5.87/6.06  thf('109', plain,
% 5.87/6.06      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.87/6.06      inference('simplify', [status(thm)], ['108'])).
% 5.87/6.06  thf('110', plain,
% 5.87/6.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.87/6.06         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 5.87/6.06          | ~ (v2_funct_1 @ X31)
% 5.87/6.06          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 5.87/6.06          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 5.87/6.06          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 5.87/6.06          | ~ (v1_funct_1 @ X31))),
% 5.87/6.06      inference('cnf', [status(esa)], [d4_tops_2])).
% 5.87/6.06  thf('111', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06             (k1_relat_1 @ sk_C))
% 5.87/6.06        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['109', '110'])).
% 5.87/6.06  thf('112', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.87/6.06      inference('demod', [status(thm)], ['56', '57'])).
% 5.87/6.06  thf('113', plain,
% 5.87/6.06      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X24)
% 5.87/6.06          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.87/6.06          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 5.87/6.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.87/6.06          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.87/6.06          | ~ (v1_funct_1 @ X24))),
% 5.87/6.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.87/6.06  thf('114', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.87/6.06        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06            != (k2_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['112', '113'])).
% 5.87/6.06  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('116', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['68', '69'])).
% 5.87/6.06  thf('117', plain,
% 5.87/6.06      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['83', '84'])).
% 5.87/6.06  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('119', plain,
% 5.87/6.06      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 5.87/6.06  thf('120', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['119'])).
% 5.87/6.06  thf('121', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('122', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('demod', [status(thm)], ['91', '92'])).
% 5.87/6.06  thf('123', plain,
% 5.87/6.06      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X24)
% 5.87/6.06          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.87/6.06          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 5.87/6.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.87/6.06          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.87/6.06          | ~ (v1_funct_1 @ X24))),
% 5.87/6.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.87/6.06  thf('124', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C))
% 5.87/6.06        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06            != (u1_struct_0 @ sk_B))
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['122', '123'])).
% 5.87/6.06  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('126', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('demod', [status(thm)], ['97', '98'])).
% 5.87/6.06  thf('127', plain,
% 5.87/6.06      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['100', '101'])).
% 5.87/6.06  thf('128', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('129', plain,
% 5.87/6.06      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06         (k1_relat_1 @ sk_C))
% 5.87/6.06        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 5.87/6.06      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 5.87/6.06  thf('130', plain,
% 5.87/6.06      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B)
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['121', '129'])).
% 5.87/6.06  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('132', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('133', plain,
% 5.87/6.06      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['130', '131', '132'])).
% 5.87/6.06  thf('134', plain,
% 5.87/6.06      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06        (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['133'])).
% 5.87/6.06  thf('135', plain,
% 5.87/6.06      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['111', '120', '134'])).
% 5.87/6.06  thf('136', plain,
% 5.87/6.06      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.87/6.06      inference('simplify', [status(thm)], ['108'])).
% 5.87/6.06  thf('137', plain,
% 5.87/6.06      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.87/6.06         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 5.87/6.06          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 5.87/6.06      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.87/6.06  thf('138', plain,
% 5.87/6.06      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['136', '137'])).
% 5.87/6.06  thf('139', plain,
% 5.87/6.06      (![X0 : $i]:
% 5.87/6.06         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.87/6.06          | ~ (v2_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_relat_1 @ X0))),
% 5.87/6.06      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.87/6.06  thf(t55_funct_1, axiom,
% 5.87/6.06    (![A:$i]:
% 5.87/6.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.87/6.06       ( ( v2_funct_1 @ A ) =>
% 5.87/6.06         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.87/6.06           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.87/6.06  thf('140', plain,
% 5.87/6.06      (![X1 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X1)
% 5.87/6.06          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 5.87/6.06          | ~ (v1_funct_1 @ X1)
% 5.87/6.06          | ~ (v1_relat_1 @ X1))),
% 5.87/6.06      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.87/6.06  thf('141', plain,
% 5.87/6.06      (![X1 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X1)
% 5.87/6.06          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 5.87/6.06          | ~ (v1_funct_1 @ X1)
% 5.87/6.06          | ~ (v1_relat_1 @ X1))),
% 5.87/6.06      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.87/6.06  thf('142', plain,
% 5.87/6.06      (![X0 : $i]:
% 5.87/6.06         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.87/6.06          | ~ (v2_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_relat_1 @ X0))),
% 5.87/6.06      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.87/6.06  thf('143', plain,
% 5.87/6.06      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.87/6.06      inference('simplify', [status(thm)], ['108'])).
% 5.87/6.06  thf('144', plain,
% 5.87/6.06      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X24)
% 5.87/6.06          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.87/6.06          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 5.87/6.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.87/6.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.87/6.06          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.87/6.06          | ~ (v1_funct_1 @ X24))),
% 5.87/6.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.87/6.06  thf('145', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06             (k1_relat_1 @ sk_C))
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.87/6.06        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['143', '144'])).
% 5.87/6.06  thf('146', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['119'])).
% 5.87/6.06  thf('147', plain,
% 5.87/6.06      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06        (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['133'])).
% 5.87/6.06  thf('148', plain,
% 5.87/6.06      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06         (k1_zfmisc_1 @ 
% 5.87/6.06          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.87/6.06        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['145', '146', '147'])).
% 5.87/6.06  thf('149', plain,
% 5.87/6.06      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['136', '137'])).
% 5.87/6.06  thf('150', plain,
% 5.87/6.06      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06         (k1_zfmisc_1 @ 
% 5.87/6.06          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.87/6.06        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['148', '149'])).
% 5.87/6.06  thf('151', plain,
% 5.87/6.06      ((~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['142', '150'])).
% 5.87/6.06  thf('152', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf(cc1_relset_1, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i]:
% 5.87/6.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.87/6.06       ( v1_relat_1 @ C ) ))).
% 5.87/6.06  thf('153', plain,
% 5.87/6.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.87/6.06         ((v1_relat_1 @ X3)
% 5.87/6.06          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 5.87/6.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.87/6.06  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('157', plain,
% 5.87/6.06      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.87/6.06      inference('demod', [status(thm)], ['151', '154', '155', '156'])).
% 5.87/6.06  thf('158', plain,
% 5.87/6.06      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['141', '157'])).
% 5.87/6.06  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('162', plain,
% 5.87/6.06      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 5.87/6.06      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 5.87/6.06  thf('163', plain,
% 5.87/6.06      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('simplify', [status(thm)], ['162'])).
% 5.87/6.06  thf('164', plain,
% 5.87/6.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.87/6.06         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 5.87/6.06          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 5.87/6.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.87/6.06  thf('165', plain,
% 5.87/6.06      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.87/6.06         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['163', '164'])).
% 5.87/6.06  thf('166', plain,
% 5.87/6.06      (![X2 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X2)
% 5.87/6.06          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 5.87/6.06          | ~ (v1_funct_1 @ X2)
% 5.87/6.06          | ~ (v1_relat_1 @ X2))),
% 5.87/6.06      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.87/6.06  thf('167', plain,
% 5.87/6.06      (![X1 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X1)
% 5.87/6.06          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 5.87/6.06          | ~ (v1_funct_1 @ X1)
% 5.87/6.06          | ~ (v1_relat_1 @ X1))),
% 5.87/6.06      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.87/6.06  thf('168', plain,
% 5.87/6.06      (![X0 : $i]:
% 5.87/6.06         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.87/6.06          | ~ (v2_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_relat_1 @ X0))),
% 5.87/6.06      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.87/6.06  thf('169', plain,
% 5.87/6.06      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 5.87/6.06      inference('simplify', [status(thm)], ['108'])).
% 5.87/6.06  thf('170', plain,
% 5.87/6.06      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X24)
% 5.87/6.06          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.87/6.06          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 5.87/6.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.87/6.06          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.87/6.06          | ~ (v1_funct_1 @ X24))),
% 5.87/6.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.87/6.06  thf('171', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06             (k1_relat_1 @ sk_C))
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['169', '170'])).
% 5.87/6.06  thf('172', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['119'])).
% 5.87/6.06  thf('173', plain,
% 5.87/6.06      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06        (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['133'])).
% 5.87/6.06  thf('174', plain,
% 5.87/6.06      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['171', '172', '173'])).
% 5.87/6.06  thf('175', plain,
% 5.87/6.06      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['136', '137'])).
% 5.87/6.06  thf('176', plain,
% 5.87/6.06      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['174', '175'])).
% 5.87/6.06  thf('177', plain,
% 5.87/6.06      ((~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['168', '176'])).
% 5.87/6.06  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('181', plain,
% 5.87/6.06      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.87/6.06      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 5.87/6.06  thf('182', plain,
% 5.87/6.06      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['167', '181'])).
% 5.87/6.06  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('186', plain,
% 5.87/6.06      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 5.87/6.06        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.87/6.06      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 5.87/6.06  thf('187', plain,
% 5.87/6.06      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('simplify', [status(thm)], ['186'])).
% 5.87/6.06  thf('188', plain,
% 5.87/6.06      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.87/6.06         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 5.87/6.06          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 5.87/6.06          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.87/6.06  thf('189', plain,
% 5.87/6.06      ((~ (zip_tseitin_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 5.87/6.06           (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 5.87/6.06        | ((k1_relat_1 @ sk_C)
% 5.87/6.06            = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06               (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['187', '188'])).
% 5.87/6.06  thf('190', plain,
% 5.87/6.06      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | ((k1_relat_1 @ sk_C)
% 5.87/6.06            = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06               (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['166', '189'])).
% 5.87/6.06  thf('191', plain,
% 5.87/6.06      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.87/6.06      inference('sup+', [status(thm)], ['12', '13'])).
% 5.87/6.06  thf('192', plain,
% 5.87/6.06      (![X27 : $i]:
% 5.87/6.06         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 5.87/6.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.87/6.06  thf('193', plain,
% 5.87/6.06      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.87/6.06        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['15', '16'])).
% 5.87/6.06  thf('194', plain,
% 5.87/6.06      ((~ (zip_tseitin_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 5.87/6.06        | ~ (l1_struct_0 @ sk_B)
% 5.87/6.06        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['192', '193'])).
% 5.87/6.06  thf('195', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 5.87/6.06      inference('sup+', [status(thm)], ['30', '31'])).
% 5.87/6.06  thf('196', plain, ((l1_struct_0 @ sk_B)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('197', plain,
% 5.87/6.06      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))
% 5.87/6.06        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 5.87/6.06      inference('demod', [status(thm)], ['194', '195', '196'])).
% 5.87/6.06  thf('198', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('199', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['34', '41'])).
% 5.87/6.06  thf('200', plain,
% 5.87/6.06      ((~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 5.87/6.06        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['197', '198', '199'])).
% 5.87/6.06  thf('201', plain,
% 5.87/6.06      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 5.87/6.06        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['191', '200'])).
% 5.87/6.06  thf('202', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['39', '40'])).
% 5.87/6.06  thf('203', plain,
% 5.87/6.06      ((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('clc', [status(thm)], ['201', '202'])).
% 5.87/6.06  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('207', plain,
% 5.87/6.06      (((k1_relat_1 @ sk_C)
% 5.87/6.06         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06            (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.87/6.06      inference('demod', [status(thm)], ['190', '203', '204', '205', '206'])).
% 5.87/6.06  thf('208', plain,
% 5.87/6.06      (((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.87/6.06      inference('sup+', [status(thm)], ['165', '207'])).
% 5.87/6.06  thf('209', plain,
% 5.87/6.06      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 5.87/6.06        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('sup+', [status(thm)], ['140', '208'])).
% 5.87/6.06  thf('210', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 5.87/6.06      inference('demod', [status(thm)], ['56', '57'])).
% 5.87/6.06  thf('211', plain,
% 5.87/6.06      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.87/6.06         (~ (v2_funct_1 @ X24)
% 5.87/6.06          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 5.87/6.06          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 5.87/6.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.87/6.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 5.87/6.06          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 5.87/6.06          | ~ (v1_funct_1 @ X24))),
% 5.87/6.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.87/6.06  thf('212', plain,
% 5.87/6.06      ((~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 5.87/6.06        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06           (k1_zfmisc_1 @ 
% 5.87/6.06            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 5.87/6.06        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06            != (k2_relat_1 @ sk_C))
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['210', '211'])).
% 5.87/6.06  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('214', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['68', '69'])).
% 5.87/6.06  thf('215', plain,
% 5.87/6.06      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 5.87/6.06         = (k2_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['83', '84'])).
% 5.87/6.06  thf('216', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('217', plain,
% 5.87/6.06      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06         (k1_zfmisc_1 @ 
% 5.87/6.06          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 5.87/6.06        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['212', '213', '214', '215', '216'])).
% 5.87/6.06  thf('218', plain,
% 5.87/6.06      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 5.87/6.06      inference('simplify', [status(thm)], ['217'])).
% 5.87/6.06  thf('219', plain,
% 5.87/6.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.87/6.06         ((v1_relat_1 @ X3)
% 5.87/6.06          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 5.87/6.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.87/6.06  thf('220', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['218', '219'])).
% 5.87/6.06  thf('221', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 5.87/6.06      inference('simplify', [status(thm)], ['119'])).
% 5.87/6.06  thf('222', plain,
% 5.87/6.06      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['209', '220', '221'])).
% 5.87/6.06  thf('223', plain,
% 5.87/6.06      ((~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['139', '222'])).
% 5.87/6.06  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('227', plain,
% 5.87/6.06      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['223', '224', '225', '226'])).
% 5.87/6.06  thf('228', plain,
% 5.87/6.06      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['138', '227'])).
% 5.87/6.06  thf('229', plain,
% 5.87/6.06      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 5.87/6.06        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['135', '228'])).
% 5.87/6.06  thf('230', plain,
% 5.87/6.06      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 5.87/6.06        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.87/6.06      inference('simplify', [status(thm)], ['229'])).
% 5.87/6.06  thf('231', plain,
% 5.87/6.06      ((~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C)
% 5.87/6.06        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 5.87/6.06      inference('sup-', [status(thm)], ['89', '230'])).
% 5.87/6.06  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('235', plain,
% 5.87/6.06      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 5.87/6.06         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 5.87/6.06      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 5.87/6.06  thf('236', plain,
% 5.87/6.06      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 5.87/6.06          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 5.87/6.06      inference('demod', [status(thm)], ['88', '235'])).
% 5.87/6.06  thf('237', plain,
% 5.87/6.06      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.87/6.06           sk_C)
% 5.87/6.06        | ~ (v1_relat_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v2_funct_1 @ sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['0', '236'])).
% 5.87/6.06  thf('238', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('demod', [status(thm)], ['91', '92'])).
% 5.87/6.06  thf('239', plain,
% 5.87/6.06      ((m1_subset_1 @ sk_C @ 
% 5.87/6.06        (k1_zfmisc_1 @ 
% 5.87/6.06         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 5.87/6.06      inference('demod', [status(thm)], ['91', '92'])).
% 5.87/6.06  thf(reflexivity_r2_funct_2, axiom,
% 5.87/6.06    (![A:$i,B:$i,C:$i,D:$i]:
% 5.87/6.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.87/6.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.87/6.06         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.87/6.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.87/6.06       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 5.87/6.06  thf('240', plain,
% 5.87/6.06      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.87/6.06         ((r2_funct_2 @ X20 @ X21 @ X22 @ X22)
% 5.87/6.06          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 5.87/6.06          | ~ (v1_funct_2 @ X22 @ X20 @ X21)
% 5.87/6.06          | ~ (v1_funct_1 @ X22)
% 5.87/6.06          | ~ (v1_funct_1 @ X23)
% 5.87/6.06          | ~ (v1_funct_2 @ X23 @ X20 @ X21)
% 5.87/6.06          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 5.87/6.06      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 5.87/6.06  thf('241', plain,
% 5.87/6.06      (![X0 : $i]:
% 5.87/6.06         (~ (m1_subset_1 @ X0 @ 
% 5.87/6.06             (k1_zfmisc_1 @ 
% 5.87/6.06              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.87/6.06          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06          | ~ (v1_funct_1 @ X0)
% 5.87/6.06          | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.87/6.06             sk_C))),
% 5.87/6.06      inference('sup-', [status(thm)], ['239', '240'])).
% 5.87/6.06  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('243', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('demod', [status(thm)], ['97', '98'])).
% 5.87/6.06  thf('244', plain,
% 5.87/6.06      (![X0 : $i]:
% 5.87/6.06         (~ (m1_subset_1 @ X0 @ 
% 5.87/6.06             (k1_zfmisc_1 @ 
% 5.87/6.06              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 5.87/6.06          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 5.87/6.06          | ~ (v1_funct_1 @ X0)
% 5.87/6.06          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 5.87/6.06             sk_C))),
% 5.87/6.06      inference('demod', [status(thm)], ['241', '242', '243'])).
% 5.87/6.06  thf('245', plain,
% 5.87/6.06      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 5.87/6.06        | ~ (v1_funct_1 @ sk_C)
% 5.87/6.06        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 5.87/6.06      inference('sup-', [status(thm)], ['238', '244'])).
% 5.87/6.06  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('247', plain,
% 5.87/6.06      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 5.87/6.06      inference('demod', [status(thm)], ['97', '98'])).
% 5.87/6.06  thf('248', plain,
% 5.87/6.06      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 5.87/6.06      inference('demod', [status(thm)], ['245', '246', '247'])).
% 5.87/6.06  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 5.87/6.06      inference('sup-', [status(thm)], ['152', '153'])).
% 5.87/6.06  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('251', plain, ((v2_funct_1 @ sk_C)),
% 5.87/6.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.87/6.06  thf('252', plain, ($false),
% 5.87/6.06      inference('demod', [status(thm)], ['237', '248', '249', '250', '251'])).
% 5.87/6.06  
% 5.87/6.06  % SZS output end Refutation
% 5.87/6.06  
% 5.87/6.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
