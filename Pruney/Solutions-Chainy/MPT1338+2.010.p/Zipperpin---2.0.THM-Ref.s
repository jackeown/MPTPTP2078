%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OoRRHgV7hG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:48 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  291 (2654 expanded)
%              Number of leaves         :   47 ( 789 expanded)
%              Depth                    :   22
%              Number of atoms          : 2331 (67607 expanded)
%              Number of equality atoms :  127 (3547 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X41 @ X42 @ X43 ) @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('28',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

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

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('46',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','46'])).

thf('48',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','28','48'])).

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

thf('50',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('54',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X41 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('58',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('60',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('61',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('64',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('66',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('67',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','67'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('71',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','73'])).

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

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
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

thf('81',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('86',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('87',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('89',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('110',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('113',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('114',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['112','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','121'])).

thf('123',plain,
    ( ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['93','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('126',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('129',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('130',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('131',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('133',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','128','131','132'])).

thf('134',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['92','133'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('135',plain,(
    ! [X8: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('136',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['79','138'])).

thf('140',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','139'])).

thf('141',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['52','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('143',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['51','144'])).

thf('146',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('148',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('149',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('150',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('152',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('153',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('156',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    zip_tseitin_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['153','156'])).

thf('158',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['150','157'])).

thf('159',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['147','158'])).

thf('160',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('161',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('162',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('164',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('165',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('167',plain,(
    zip_tseitin_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['162','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['159','168','169'])).

thf('171',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['159','168','169'])).

thf('172',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('174',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['159','168','169'])).

thf('175',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['159','168','169'])).

thf('176',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('177',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','170','171','172','173','174','175','176'])).

thf('178',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','73'])).

thf('179',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('180',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','128','131','132'])).

thf('182',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','182'])).

thf('184',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
 != ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','73'])).

thf('186',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('187',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('189',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X41 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('190',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('193',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('194',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['190','191','192','193'])).

thf('195',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('196',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X41 @ X42 @ X43 ) @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('197',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('200',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('201',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['187','194','201'])).

thf('203',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','137'])).

thf('204',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('206',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','73'])).

thf('208',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('209',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','73'])).

thf('211',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('212',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('214',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('215',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('216',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('218',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('221',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != X31 )
      | ( v1_partfun1 @ X32 @ X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('222',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v4_relat_1 @ X32 @ ( k1_relat_1 @ X32 ) )
      | ( v1_partfun1 @ X32 @ ( k1_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['220','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['219','223'])).

thf('225',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('226',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('229',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['224','225','226','227','228'])).

thf('230',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['213','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('232',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('236',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('238',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('239',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['206','209','212','239'])).

thf('241',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
 != ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['184','240'])).

thf('242',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['145','241'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OoRRHgV7hG
% 0.14/0.36  % Computer   : n013.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:07:25 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.59/1.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.59/1.79  % Solved by: fo/fo7.sh
% 1.59/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.59/1.79  % done 798 iterations in 1.309s
% 1.59/1.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.59/1.79  % SZS output start Refutation
% 1.59/1.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.59/1.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.59/1.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.59/1.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.59/1.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.59/1.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.59/1.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.59/1.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.59/1.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.59/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.59/1.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.59/1.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.59/1.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.59/1.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.59/1.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.59/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.59/1.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.59/1.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.59/1.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.59/1.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.59/1.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.59/1.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.59/1.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.59/1.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.59/1.79  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.59/1.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.59/1.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.59/1.79  thf(d3_struct_0, axiom,
% 1.59/1.79    (![A:$i]:
% 1.59/1.79     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.59/1.79  thf('0', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('1', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf(t62_tops_2, conjecture,
% 1.59/1.79    (![A:$i]:
% 1.59/1.79     ( ( l1_struct_0 @ A ) =>
% 1.59/1.79       ( ![B:$i]:
% 1.59/1.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.59/1.79           ( ![C:$i]:
% 1.59/1.79             ( ( ( v1_funct_1 @ C ) & 
% 1.59/1.79                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.59/1.79                 ( m1_subset_1 @
% 1.59/1.79                   C @ 
% 1.59/1.79                   ( k1_zfmisc_1 @
% 1.59/1.79                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.59/1.79               ( ( ( ( k2_relset_1 @
% 1.59/1.79                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.59/1.79                     ( k2_struct_0 @ B ) ) & 
% 1.59/1.79                   ( v2_funct_1 @ C ) ) =>
% 1.59/1.79                 ( ( ( k1_relset_1 @
% 1.59/1.79                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.79                       ( k2_tops_2 @
% 1.59/1.79                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.79                     ( k2_struct_0 @ B ) ) & 
% 1.59/1.79                   ( ( k2_relset_1 @
% 1.59/1.79                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.79                       ( k2_tops_2 @
% 1.59/1.79                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.79                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.59/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.59/1.79    (~( ![A:$i]:
% 1.59/1.79        ( ( l1_struct_0 @ A ) =>
% 1.59/1.79          ( ![B:$i]:
% 1.59/1.79            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.59/1.79              ( ![C:$i]:
% 1.59/1.79                ( ( ( v1_funct_1 @ C ) & 
% 1.59/1.79                    ( v1_funct_2 @
% 1.59/1.79                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.59/1.79                    ( m1_subset_1 @
% 1.59/1.79                      C @ 
% 1.59/1.79                      ( k1_zfmisc_1 @
% 1.59/1.79                        ( k2_zfmisc_1 @
% 1.59/1.79                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.59/1.79                  ( ( ( ( k2_relset_1 @
% 1.59/1.79                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.59/1.79                        ( k2_struct_0 @ B ) ) & 
% 1.59/1.79                      ( v2_funct_1 @ C ) ) =>
% 1.59/1.79                    ( ( ( k1_relset_1 @
% 1.59/1.79                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.79                          ( k2_tops_2 @
% 1.59/1.79                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.79                        ( k2_struct_0 @ B ) ) & 
% 1.59/1.79                      ( ( k2_relset_1 @
% 1.59/1.79                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.59/1.79                          ( k2_tops_2 @
% 1.59/1.79                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.59/1.79                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.59/1.79    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.59/1.79  thf('2', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('3', plain,
% 1.59/1.79      (((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79         (k1_zfmisc_1 @ 
% 1.59/1.79          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_A))),
% 1.59/1.79      inference('sup+', [status(thm)], ['1', '2'])).
% 1.59/1.79  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('5', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.59/1.79  thf('6', plain,
% 1.59/1.79      (((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79         (k1_zfmisc_1 @ 
% 1.59/1.79          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['0', '5'])).
% 1.59/1.79  thf('7', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('8', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['6', '7'])).
% 1.59/1.79  thf('9', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf(redefinition_k2_relset_1, axiom,
% 1.59/1.79    (![A:$i,B:$i,C:$i]:
% 1.59/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.59/1.79  thf('10', plain,
% 1.59/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.59/1.79         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 1.59/1.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.59/1.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.79  thf('11', plain,
% 1.59/1.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['9', '10'])).
% 1.59/1.79  thf('12', plain,
% 1.59/1.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('13', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('14', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['8', '13'])).
% 1.59/1.79  thf(dt_k2_tops_2, axiom,
% 1.59/1.79    (![A:$i,B:$i,C:$i]:
% 1.59/1.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.79       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.59/1.79         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.59/1.79         ( m1_subset_1 @
% 1.59/1.79           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.59/1.79           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.59/1.79  thf('15', plain,
% 1.59/1.79      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.59/1.79         ((v1_funct_2 @ (k2_tops_2 @ X41 @ X42 @ X43) @ X42 @ X41)
% 1.59/1.79          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.59/1.79          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.59/1.79          | ~ (v1_funct_1 @ X43))),
% 1.59/1.79      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.59/1.79  thf('16', plain,
% 1.59/1.79      ((~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | (v1_funct_2 @ 
% 1.59/1.79           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1) @ 
% 1.59/1.79           (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_A)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['14', '15'])).
% 1.59/1.79  thf('17', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('18', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('19', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('20', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('21', plain,
% 1.59/1.79      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_A))),
% 1.59/1.79      inference('sup+', [status(thm)], ['19', '20'])).
% 1.59/1.79  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('23', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['21', '22'])).
% 1.59/1.79  thf('24', plain,
% 1.59/1.79      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['18', '23'])).
% 1.59/1.79  thf('25', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('26', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['24', '25'])).
% 1.59/1.79  thf('27', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('28', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['26', '27'])).
% 1.59/1.79  thf('29', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['8', '13'])).
% 1.59/1.79  thf(d4_tops_2, axiom,
% 1.59/1.79    (![A:$i,B:$i,C:$i]:
% 1.59/1.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.79       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.59/1.79         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.59/1.79  thf('30', plain,
% 1.59/1.79      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.59/1.79         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 1.59/1.79          | ~ (v2_funct_1 @ X40)
% 1.59/1.79          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 1.59/1.79          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.59/1.79          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.59/1.79          | ~ (v1_funct_1 @ X40))),
% 1.59/1.79      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.59/1.79  thf('31', plain,
% 1.59/1.79      ((~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.59/1.79            = (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | ~ (v2_funct_1 @ sk_C_1)
% 1.59/1.79        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.59/1.79            != (k2_relat_1 @ sk_C_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['29', '30'])).
% 1.59/1.79  thf('32', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('33', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['26', '27'])).
% 1.59/1.79  thf('34', plain, ((v2_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('35', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('36', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('37', plain,
% 1.59/1.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('38', plain,
% 1.59/1.79      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79          = (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_A))),
% 1.59/1.79      inference('sup+', [status(thm)], ['36', '37'])).
% 1.59/1.79  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('40', plain,
% 1.59/1.79      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['38', '39'])).
% 1.59/1.79  thf('41', plain,
% 1.59/1.79      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79          = (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['35', '40'])).
% 1.59/1.79  thf('42', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('43', plain,
% 1.59/1.79      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['41', '42'])).
% 1.59/1.79  thf('44', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('45', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('46', plain,
% 1.59/1.79      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.59/1.79         = (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.59/1.79  thf('47', plain,
% 1.59/1.79      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.59/1.79          = (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | ((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['31', '32', '33', '34', '46'])).
% 1.59/1.79  thf('48', plain,
% 1.59/1.79      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.59/1.79         = (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('simplify', [status(thm)], ['47'])).
% 1.59/1.79  thf('49', plain,
% 1.59/1.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ 
% 1.59/1.79        (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['16', '17', '28', '48'])).
% 1.59/1.79  thf(d1_funct_2, axiom,
% 1.59/1.79    (![A:$i,B:$i,C:$i]:
% 1.59/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.59/1.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.59/1.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.59/1.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.59/1.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.59/1.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.59/1.79  thf(zf_stmt_1, axiom,
% 1.59/1.79    (![C:$i,B:$i,A:$i]:
% 1.59/1.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.59/1.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.59/1.79  thf('50', plain,
% 1.59/1.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.59/1.79         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.59/1.79          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.59/1.79          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.59/1.79  thf('51', plain,
% 1.59/1.79      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79           (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ((k2_relat_1 @ sk_C_1)
% 1.59/1.79            = (k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79               (k2_funct_1 @ sk_C_1))))),
% 1.59/1.79      inference('sup-', [status(thm)], ['49', '50'])).
% 1.59/1.79  thf('52', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('53', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.59/1.79  thf('54', plain,
% 1.59/1.79      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.59/1.79         ((m1_subset_1 @ (k2_tops_2 @ X41 @ X42 @ X43) @ 
% 1.59/1.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 1.59/1.79          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.59/1.79          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.59/1.79          | ~ (v1_funct_1 @ X43))),
% 1.59/1.79      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.59/1.79  thf('55', plain,
% 1.59/1.79      ((~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79             (u1_struct_0 @ sk_B_1))
% 1.59/1.79        | (m1_subset_1 @ 
% 1.59/1.79           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1) @ 
% 1.59/1.79           (k1_zfmisc_1 @ 
% 1.59/1.79            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A)))))),
% 1.59/1.79      inference('sup-', [status(thm)], ['53', '54'])).
% 1.59/1.79  thf('56', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('57', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['21', '22'])).
% 1.59/1.79  thf('58', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('59', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.59/1.79  thf('60', plain,
% 1.59/1.79      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.59/1.79         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 1.59/1.79          | ~ (v2_funct_1 @ X40)
% 1.59/1.79          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 1.59/1.79          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.59/1.79          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.59/1.79          | ~ (v1_funct_1 @ X40))),
% 1.59/1.79      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.59/1.79  thf('61', plain,
% 1.59/1.79      ((~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79             (u1_struct_0 @ sk_B_1))
% 1.59/1.79        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79            = (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | ~ (v2_funct_1 @ sk_C_1)
% 1.59/1.79        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.59/1.79            sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['59', '60'])).
% 1.59/1.79  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('63', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['21', '22'])).
% 1.59/1.79  thf('64', plain, ((v2_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('65', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.59/1.79  thf('66', plain,
% 1.59/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.59/1.79         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 1.59/1.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.59/1.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.79  thf('67', plain,
% 1.59/1.79      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['65', '66'])).
% 1.59/1.79  thf('68', plain,
% 1.59/1.79      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79          = (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['61', '62', '63', '64', '67'])).
% 1.59/1.79  thf('69', plain,
% 1.59/1.79      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1)
% 1.59/1.79        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79            = (k2_funct_1 @ sk_C_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['58', '68'])).
% 1.59/1.79  thf('70', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('71', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('72', plain,
% 1.59/1.79      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79            = (k2_funct_1 @ sk_C_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.59/1.79  thf('73', plain,
% 1.59/1.79      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('simplify', [status(thm)], ['72'])).
% 1.59/1.79  thf('74', plain,
% 1.59/1.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.79      inference('demod', [status(thm)], ['55', '56', '57', '73'])).
% 1.59/1.79  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.59/1.79  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.59/1.79  thf(zf_stmt_4, axiom,
% 1.59/1.79    (![B:$i,A:$i]:
% 1.59/1.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.59/1.79       ( zip_tseitin_0 @ B @ A ) ))).
% 1.59/1.79  thf(zf_stmt_5, axiom,
% 1.59/1.79    (![A:$i,B:$i,C:$i]:
% 1.59/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.59/1.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.59/1.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.59/1.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.59/1.79  thf('75', plain,
% 1.59/1.79      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.59/1.79         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.59/1.79          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.59/1.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.59/1.79  thf('76', plain,
% 1.59/1.79      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79         (u1_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['74', '75'])).
% 1.59/1.79  thf('77', plain,
% 1.59/1.79      (![X23 : $i, X24 : $i]:
% 1.59/1.79         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.59/1.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.59/1.79  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.59/1.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.59/1.79  thf('79', plain,
% 1.59/1.79      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['77', '78'])).
% 1.59/1.79  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf(t55_funct_1, axiom,
% 1.59/1.79    (![A:$i]:
% 1.59/1.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.79       ( ( v2_funct_1 @ A ) =>
% 1.59/1.79         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.59/1.79           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.59/1.79  thf('81', plain,
% 1.59/1.79      (![X10 : $i]:
% 1.59/1.79         (~ (v2_funct_1 @ X10)
% 1.59/1.79          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.79          | ~ (v1_funct_1 @ X10)
% 1.59/1.79          | ~ (v1_relat_1 @ X10))),
% 1.59/1.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.79  thf('82', plain,
% 1.59/1.79      ((~ (v1_relat_1 @ sk_C_1)
% 1.59/1.79        | ((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.59/1.79        | ~ (v2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['80', '81'])).
% 1.59/1.79  thf('83', plain, ((v2_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('84', plain,
% 1.59/1.79      ((~ (v1_relat_1 @ sk_C_1)
% 1.59/1.79        | ((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['82', '83'])).
% 1.59/1.79  thf('85', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf(cc1_relset_1, axiom,
% 1.59/1.79    (![A:$i,B:$i,C:$i]:
% 1.59/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.79       ( v1_relat_1 @ C ) ))).
% 1.59/1.79  thf('86', plain,
% 1.59/1.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.59/1.79         ((v1_relat_1 @ X11)
% 1.59/1.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.59/1.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.59/1.79  thf('87', plain, ((v1_relat_1 @ sk_C_1)),
% 1.59/1.79      inference('sup-', [status(thm)], ['85', '86'])).
% 1.59/1.79  thf('88', plain,
% 1.59/1.79      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['84', '87'])).
% 1.59/1.79  thf(fc8_relat_1, axiom,
% 1.59/1.79    (![A:$i]:
% 1.59/1.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.59/1.79       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 1.59/1.79  thf('89', plain,
% 1.59/1.79      (![X9 : $i]:
% 1.59/1.79         (~ (v1_xboole_0 @ (k1_relat_1 @ X9))
% 1.59/1.79          | ~ (v1_relat_1 @ X9)
% 1.59/1.79          | (v1_xboole_0 @ X9))),
% 1.59/1.79      inference('cnf', [status(esa)], [fc8_relat_1])).
% 1.59/1.79  thf('90', plain,
% 1.59/1.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.59/1.79        | (v1_xboole_0 @ sk_C_1)
% 1.59/1.79        | ~ (v1_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['88', '89'])).
% 1.59/1.79  thf('91', plain, ((v1_relat_1 @ sk_C_1)),
% 1.59/1.79      inference('sup-', [status(thm)], ['85', '86'])).
% 1.59/1.79  thf('92', plain,
% 1.59/1.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.59/1.79        | (v1_xboole_0 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['90', '91'])).
% 1.59/1.79  thf('93', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('94', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('95', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('96', plain,
% 1.59/1.79      (((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79         (k1_zfmisc_1 @ 
% 1.59/1.79          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['94', '95'])).
% 1.59/1.79  thf('97', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('98', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['96', '97'])).
% 1.59/1.79  thf('99', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('100', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['98', '99'])).
% 1.59/1.79  thf(cc5_funct_2, axiom,
% 1.59/1.79    (![A:$i,B:$i]:
% 1.59/1.79     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.59/1.79       ( ![C:$i]:
% 1.59/1.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.79           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.59/1.79             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.59/1.79  thf('101', plain,
% 1.59/1.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.59/1.79         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.59/1.79          | (v1_partfun1 @ X20 @ X21)
% 1.59/1.79          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 1.59/1.79          | ~ (v1_funct_1 @ X20)
% 1.59/1.79          | (v1_xboole_0 @ X22))),
% 1.59/1.79      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.59/1.79  thf('102', plain,
% 1.59/1.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['100', '101'])).
% 1.59/1.79  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('104', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('105', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('106', plain,
% 1.59/1.79      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['104', '105'])).
% 1.59/1.79  thf('107', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('108', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['106', '107'])).
% 1.59/1.79  thf('109', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('110', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['108', '109'])).
% 1.59/1.79  thf('111', plain,
% 1.59/1.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 1.59/1.79      inference('demod', [status(thm)], ['102', '103', '110'])).
% 1.59/1.79  thf('112', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('113', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf(fc2_struct_0, axiom,
% 1.59/1.79    (![A:$i]:
% 1.59/1.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.59/1.79       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.59/1.79  thf('114', plain,
% 1.59/1.79      (![X34 : $i]:
% 1.59/1.79         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 1.59/1.79          | ~ (l1_struct_0 @ X34)
% 1.59/1.79          | (v2_struct_0 @ X34))),
% 1.59/1.79      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.59/1.79  thf('115', plain,
% 1.59/1.79      (![X0 : $i]:
% 1.59/1.79         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.59/1.79          | ~ (l1_struct_0 @ X0)
% 1.59/1.79          | (v2_struct_0 @ X0)
% 1.59/1.79          | ~ (l1_struct_0 @ X0))),
% 1.59/1.79      inference('sup-', [status(thm)], ['113', '114'])).
% 1.59/1.79  thf('116', plain,
% 1.59/1.79      (![X0 : $i]:
% 1.59/1.79         ((v2_struct_0 @ X0)
% 1.59/1.79          | ~ (l1_struct_0 @ X0)
% 1.59/1.79          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.59/1.79      inference('simplify', [status(thm)], ['115'])).
% 1.59/1.79  thf('117', plain,
% 1.59/1.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1)
% 1.59/1.79        | (v2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['112', '116'])).
% 1.59/1.79  thf('118', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('119', plain,
% 1.59/1.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['117', '118'])).
% 1.59/1.79  thf('120', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('121', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('clc', [status(thm)], ['119', '120'])).
% 1.59/1.79  thf('122', plain, ((v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.59/1.79      inference('clc', [status(thm)], ['111', '121'])).
% 1.59/1.79  thf('123', plain,
% 1.59/1.79      (((v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.59/1.79      inference('sup+', [status(thm)], ['93', '122'])).
% 1.59/1.79  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('125', plain, ((v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['123', '124'])).
% 1.59/1.79  thf(d4_partfun1, axiom,
% 1.59/1.79    (![A:$i,B:$i]:
% 1.59/1.79     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.59/1.79       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.59/1.79  thf('126', plain,
% 1.59/1.79      (![X31 : $i, X32 : $i]:
% 1.59/1.79         (~ (v1_partfun1 @ X32 @ X31)
% 1.59/1.79          | ((k1_relat_1 @ X32) = (X31))
% 1.59/1.79          | ~ (v4_relat_1 @ X32 @ X31)
% 1.59/1.79          | ~ (v1_relat_1 @ X32))),
% 1.59/1.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.59/1.79  thf('127', plain,
% 1.59/1.79      ((~ (v1_relat_1 @ sk_C_1)
% 1.59/1.79        | ~ (v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))
% 1.59/1.79        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['125', '126'])).
% 1.59/1.79  thf('128', plain, ((v1_relat_1 @ sk_C_1)),
% 1.59/1.79      inference('sup-', [status(thm)], ['85', '86'])).
% 1.59/1.79  thf('129', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.59/1.79  thf(cc2_relset_1, axiom,
% 1.59/1.79    (![A:$i,B:$i,C:$i]:
% 1.59/1.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.79       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.59/1.79  thf('130', plain,
% 1.59/1.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.59/1.79         ((v4_relat_1 @ X14 @ X15)
% 1.59/1.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.59/1.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.59/1.79  thf('131', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('sup-', [status(thm)], ['129', '130'])).
% 1.59/1.79  thf('132', plain,
% 1.59/1.79      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['84', '87'])).
% 1.59/1.79  thf('133', plain,
% 1.59/1.79      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['127', '128', '131', '132'])).
% 1.59/1.79  thf('134', plain,
% 1.59/1.79      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['92', '133'])).
% 1.59/1.79  thf(fc11_relat_1, axiom,
% 1.59/1.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 1.59/1.79  thf('135', plain,
% 1.59/1.79      (![X8 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 1.59/1.79      inference('cnf', [status(esa)], [fc11_relat_1])).
% 1.59/1.79  thf('136', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('clc', [status(thm)], ['119', '120'])).
% 1.59/1.79  thf('137', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.59/1.79      inference('sup-', [status(thm)], ['135', '136'])).
% 1.59/1.79  thf('138', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('clc', [status(thm)], ['134', '137'])).
% 1.59/1.79  thf('139', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ X0)),
% 1.59/1.79      inference('sup-', [status(thm)], ['79', '138'])).
% 1.59/1.79  thf('140', plain,
% 1.59/1.79      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79        (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['76', '139'])).
% 1.59/1.79  thf('141', plain,
% 1.59/1.79      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79         (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['52', '140'])).
% 1.59/1.79  thf('142', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('143', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('144', plain,
% 1.59/1.79      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79        (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['141', '142', '143'])).
% 1.59/1.79  thf('145', plain,
% 1.59/1.79      (((k2_relat_1 @ sk_C_1)
% 1.59/1.79         = (k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79            (k2_funct_1 @ sk_C_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['51', '144'])).
% 1.59/1.79  thf('146', plain,
% 1.59/1.79      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.59/1.79          != (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.59/1.79            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.59/1.79            != (k2_struct_0 @ sk_A)))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('147', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('148', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['108', '109'])).
% 1.59/1.79  thf('149', plain,
% 1.59/1.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.59/1.79         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.59/1.79          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.59/1.79          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.59/1.79  thf('150', plain,
% 1.59/1.79      ((~ (zip_tseitin_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ 
% 1.59/1.79           (u1_struct_0 @ sk_A))
% 1.59/1.79        | ((u1_struct_0 @ sk_A)
% 1.59/1.79            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ 
% 1.59/1.79               sk_C_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['148', '149'])).
% 1.59/1.79  thf('151', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['98', '99'])).
% 1.59/1.79  thf('152', plain,
% 1.59/1.79      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.59/1.79         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.59/1.79          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.59/1.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.59/1.79  thf('153', plain,
% 1.59/1.79      (((zip_tseitin_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 1.59/1.79        | ~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['151', '152'])).
% 1.59/1.79  thf('154', plain,
% 1.59/1.79      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['77', '78'])).
% 1.59/1.79  thf('155', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('clc', [status(thm)], ['119', '120'])).
% 1.59/1.79  thf('156', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C_1) @ X0)),
% 1.59/1.79      inference('sup-', [status(thm)], ['154', '155'])).
% 1.59/1.79  thf('157', plain,
% 1.59/1.79      ((zip_tseitin_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['153', '156'])).
% 1.59/1.79  thf('158', plain,
% 1.59/1.79      (((u1_struct_0 @ sk_A)
% 1.59/1.79         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['150', '157'])).
% 1.59/1.79  thf('159', plain,
% 1.59/1.79      ((((u1_struct_0 @ sk_A)
% 1.59/1.79          = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ 
% 1.59/1.79             sk_C_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_A))),
% 1.59/1.79      inference('sup+', [status(thm)], ['147', '158'])).
% 1.59/1.79  thf('160', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['26', '27'])).
% 1.59/1.79  thf('161', plain,
% 1.59/1.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.59/1.79         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 1.59/1.79          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 1.59/1.79          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.59/1.79  thf('162', plain,
% 1.59/1.79      ((~ (zip_tseitin_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ 
% 1.59/1.79           (k2_struct_0 @ sk_A))
% 1.59/1.79        | ((k2_struct_0 @ sk_A)
% 1.59/1.79            = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ 
% 1.59/1.79               sk_C_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['160', '161'])).
% 1.59/1.79  thf('163', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['8', '13'])).
% 1.59/1.79  thf('164', plain,
% 1.59/1.79      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.59/1.79         (~ (zip_tseitin_0 @ X28 @ X29)
% 1.59/1.79          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 1.59/1.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.59/1.79  thf('165', plain,
% 1.59/1.79      (((zip_tseitin_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_A))
% 1.59/1.79        | ~ (zip_tseitin_0 @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_A)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['163', '164'])).
% 1.59/1.79  thf('166', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_relat_1 @ sk_C_1) @ X0)),
% 1.59/1.79      inference('sup-', [status(thm)], ['154', '155'])).
% 1.59/1.79  thf('167', plain,
% 1.59/1.79      ((zip_tseitin_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['165', '166'])).
% 1.59/1.79  thf('168', plain,
% 1.59/1.79      (((k2_struct_0 @ sk_A)
% 1.59/1.79         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['162', '167'])).
% 1.59/1.79  thf('169', plain, ((l1_struct_0 @ sk_A)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('170', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['159', '168', '169'])).
% 1.59/1.79  thf('171', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['159', '168', '169'])).
% 1.59/1.79  thf('172', plain,
% 1.59/1.79      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('simplify', [status(thm)], ['72'])).
% 1.59/1.79  thf('173', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('174', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['159', '168', '169'])).
% 1.59/1.79  thf('175', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['159', '168', '169'])).
% 1.59/1.79  thf('176', plain,
% 1.59/1.79      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('simplify', [status(thm)], ['72'])).
% 1.59/1.79  thf('177', plain,
% 1.59/1.79      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79          (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79            (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A)))),
% 1.59/1.79      inference('demod', [status(thm)],
% 1.59/1.79                ['146', '170', '171', '172', '173', '174', '175', '176'])).
% 1.59/1.79  thf('178', plain,
% 1.59/1.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.79      inference('demod', [status(thm)], ['55', '56', '57', '73'])).
% 1.59/1.79  thf('179', plain,
% 1.59/1.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.59/1.79         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 1.59/1.79          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.59/1.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.79  thf('180', plain,
% 1.59/1.79      (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79         (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['178', '179'])).
% 1.59/1.79  thf('181', plain,
% 1.59/1.79      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['127', '128', '131', '132'])).
% 1.59/1.79  thf('182', plain,
% 1.59/1.79      (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79         (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['180', '181'])).
% 1.59/1.79  thf('183', plain,
% 1.59/1.79      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79          (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 1.59/1.79      inference('demod', [status(thm)], ['177', '182'])).
% 1.59/1.79  thf('184', plain,
% 1.59/1.79      (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79         (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('simplify', [status(thm)], ['183'])).
% 1.59/1.79  thf('185', plain,
% 1.59/1.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.79      inference('demod', [status(thm)], ['55', '56', '57', '73'])).
% 1.59/1.79  thf('186', plain,
% 1.59/1.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.59/1.79         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.59/1.79          | (v1_partfun1 @ X20 @ X21)
% 1.59/1.79          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 1.59/1.79          | ~ (v1_funct_1 @ X20)
% 1.59/1.79          | (v1_xboole_0 @ X22))),
% 1.59/1.79      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.59/1.79  thf('187', plain,
% 1.59/1.79      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.59/1.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.59/1.79             (k2_struct_0 @ sk_A))
% 1.59/1.79        | (v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['185', '186'])).
% 1.59/1.79  thf('188', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.59/1.79  thf('189', plain,
% 1.59/1.79      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.59/1.79         ((v1_funct_1 @ (k2_tops_2 @ X41 @ X42 @ X43))
% 1.59/1.79          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.59/1.79          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.59/1.79          | ~ (v1_funct_1 @ X43))),
% 1.59/1.79      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.59/1.79  thf('190', plain,
% 1.59/1.79      ((~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79             (u1_struct_0 @ sk_B_1))
% 1.59/1.79        | (v1_funct_1 @ 
% 1.59/1.79           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['188', '189'])).
% 1.59/1.79  thf('191', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('192', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['21', '22'])).
% 1.59/1.79  thf('193', plain,
% 1.59/1.79      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('simplify', [status(thm)], ['72'])).
% 1.59/1.79  thf('194', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['190', '191', '192', '193'])).
% 1.59/1.79  thf('195', plain,
% 1.59/1.79      ((m1_subset_1 @ sk_C_1 @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.59/1.79      inference('demod', [status(thm)], ['3', '4'])).
% 1.59/1.79  thf('196', plain,
% 1.59/1.79      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.59/1.79         ((v1_funct_2 @ (k2_tops_2 @ X41 @ X42 @ X43) @ X42 @ X41)
% 1.59/1.79          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.59/1.79          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.59/1.79          | ~ (v1_funct_1 @ X43))),
% 1.59/1.79      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.59/1.79  thf('197', plain,
% 1.59/1.79      ((~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79             (u1_struct_0 @ sk_B_1))
% 1.59/1.79        | (v1_funct_2 @ 
% 1.59/1.79           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1) @ 
% 1.59/1.79           (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['195', '196'])).
% 1.59/1.79  thf('198', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('199', plain,
% 1.59/1.79      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['21', '22'])).
% 1.59/1.79  thf('200', plain,
% 1.59/1.79      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.59/1.79         = (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('simplify', [status(thm)], ['72'])).
% 1.59/1.79  thf('201', plain,
% 1.59/1.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.59/1.79        (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 1.59/1.79  thf('202', plain,
% 1.59/1.79      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.59/1.79        | (v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['187', '194', '201'])).
% 1.59/1.79  thf('203', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.59/1.79      inference('clc', [status(thm)], ['134', '137'])).
% 1.59/1.79  thf('204', plain,
% 1.59/1.79      ((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('clc', [status(thm)], ['202', '203'])).
% 1.59/1.79  thf('205', plain,
% 1.59/1.79      (![X31 : $i, X32 : $i]:
% 1.59/1.79         (~ (v1_partfun1 @ X32 @ X31)
% 1.59/1.79          | ((k1_relat_1 @ X32) = (X31))
% 1.59/1.79          | ~ (v4_relat_1 @ X32 @ X31)
% 1.59/1.79          | ~ (v1_relat_1 @ X32))),
% 1.59/1.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.59/1.79  thf('206', plain,
% 1.59/1.79      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))
% 1.59/1.79        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['204', '205'])).
% 1.59/1.79  thf('207', plain,
% 1.59/1.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.79      inference('demod', [status(thm)], ['55', '56', '57', '73'])).
% 1.59/1.79  thf('208', plain,
% 1.59/1.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.59/1.79         ((v1_relat_1 @ X11)
% 1.59/1.79          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.59/1.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.59/1.79  thf('209', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['207', '208'])).
% 1.59/1.79  thf('210', plain,
% 1.59/1.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.59/1.79        (k1_zfmisc_1 @ 
% 1.59/1.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_A))))),
% 1.59/1.79      inference('demod', [status(thm)], ['55', '56', '57', '73'])).
% 1.59/1.79  thf('211', plain,
% 1.59/1.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.59/1.79         ((v4_relat_1 @ X14 @ X15)
% 1.59/1.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.59/1.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.59/1.79  thf('212', plain,
% 1.59/1.79      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['210', '211'])).
% 1.59/1.79  thf('213', plain,
% 1.59/1.79      (![X10 : $i]:
% 1.59/1.79         (~ (v2_funct_1 @ X10)
% 1.59/1.79          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.79          | ~ (v1_funct_1 @ X10)
% 1.59/1.79          | ~ (v1_relat_1 @ X10))),
% 1.59/1.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.79  thf('214', plain,
% 1.59/1.79      (![X33 : $i]:
% 1.59/1.79         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 1.59/1.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.59/1.79  thf('215', plain,
% 1.59/1.79      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['210', '211'])).
% 1.59/1.79  thf('216', plain,
% 1.59/1.79      (((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B_1))
% 1.59/1.79        | ~ (l1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['214', '215'])).
% 1.59/1.79  thf('217', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['11', '12'])).
% 1.59/1.79  thf('218', plain, ((l1_struct_0 @ sk_B_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('219', plain,
% 1.59/1.79      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['216', '217', '218'])).
% 1.59/1.79  thf('220', plain,
% 1.59/1.79      (![X10 : $i]:
% 1.59/1.79         (~ (v2_funct_1 @ X10)
% 1.59/1.79          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.79          | ~ (v1_funct_1 @ X10)
% 1.59/1.79          | ~ (v1_relat_1 @ X10))),
% 1.59/1.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.79  thf('221', plain,
% 1.59/1.79      (![X31 : $i, X32 : $i]:
% 1.59/1.79         (((k1_relat_1 @ X32) != (X31))
% 1.59/1.79          | (v1_partfun1 @ X32 @ X31)
% 1.59/1.79          | ~ (v4_relat_1 @ X32 @ X31)
% 1.59/1.79          | ~ (v1_relat_1 @ X32))),
% 1.59/1.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.59/1.79  thf('222', plain,
% 1.59/1.79      (![X32 : $i]:
% 1.59/1.79         (~ (v1_relat_1 @ X32)
% 1.59/1.79          | ~ (v4_relat_1 @ X32 @ (k1_relat_1 @ X32))
% 1.59/1.79          | (v1_partfun1 @ X32 @ (k1_relat_1 @ X32)))),
% 1.59/1.79      inference('simplify', [status(thm)], ['221'])).
% 1.59/1.79  thf('223', plain,
% 1.59/1.79      (![X0 : $i]:
% 1.59/1.79         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.59/1.79          | ~ (v1_relat_1 @ X0)
% 1.59/1.79          | ~ (v1_funct_1 @ X0)
% 1.59/1.79          | ~ (v2_funct_1 @ X0)
% 1.59/1.79          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['220', '222'])).
% 1.59/1.79  thf('224', plain,
% 1.59/1.79      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | (v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.59/1.79           (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 1.59/1.79        | ~ (v2_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['219', '223'])).
% 1.59/1.79  thf('225', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['207', '208'])).
% 1.59/1.79  thf('226', plain, ((v2_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('227', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('228', plain, ((v1_relat_1 @ sk_C_1)),
% 1.59/1.79      inference('sup-', [status(thm)], ['85', '86'])).
% 1.59/1.79  thf('229', plain,
% 1.59/1.79      ((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.59/1.79        (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.59/1.79      inference('demod', [status(thm)], ['224', '225', '226', '227', '228'])).
% 1.59/1.79  thf('230', plain,
% 1.59/1.79      (((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ~ (v1_relat_1 @ sk_C_1)
% 1.59/1.79        | ~ (v1_funct_1 @ sk_C_1)
% 1.59/1.79        | ~ (v2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('sup+', [status(thm)], ['213', '229'])).
% 1.59/1.79  thf('231', plain, ((v1_relat_1 @ sk_C_1)),
% 1.59/1.79      inference('sup-', [status(thm)], ['85', '86'])).
% 1.59/1.79  thf('232', plain, ((v1_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('233', plain, ((v2_funct_1 @ sk_C_1)),
% 1.59/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.79  thf('234', plain,
% 1.59/1.79      ((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 1.59/1.79  thf('235', plain,
% 1.59/1.79      (![X31 : $i, X32 : $i]:
% 1.59/1.79         (~ (v1_partfun1 @ X32 @ X31)
% 1.59/1.79          | ((k1_relat_1 @ X32) = (X31))
% 1.59/1.79          | ~ (v4_relat_1 @ X32 @ X31)
% 1.59/1.79          | ~ (v1_relat_1 @ X32))),
% 1.59/1.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.59/1.79  thf('236', plain,
% 1.59/1.79      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 1.59/1.79        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 1.59/1.79        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1)))),
% 1.59/1.79      inference('sup-', [status(thm)], ['234', '235'])).
% 1.59/1.79  thf('237', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 1.59/1.79      inference('sup-', [status(thm)], ['207', '208'])).
% 1.59/1.79  thf('238', plain,
% 1.59/1.79      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['216', '217', '218'])).
% 1.59/1.79  thf('239', plain,
% 1.59/1.79      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['236', '237', '238'])).
% 1.59/1.79  thf('240', plain, (((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['206', '209', '212', '239'])).
% 1.59/1.79  thf('241', plain,
% 1.59/1.79      (((k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_A) @ 
% 1.59/1.79         (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1))),
% 1.59/1.79      inference('demod', [status(thm)], ['184', '240'])).
% 1.59/1.79  thf('242', plain, ($false),
% 1.59/1.79      inference('simplify_reflect-', [status(thm)], ['145', '241'])).
% 1.59/1.79  
% 1.59/1.79  % SZS output end Refutation
% 1.59/1.79  
% 1.59/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
