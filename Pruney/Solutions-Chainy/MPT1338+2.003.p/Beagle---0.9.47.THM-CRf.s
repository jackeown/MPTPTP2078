%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:13 EST 2020

% Result     : Theorem 11.36s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :  300 (15692 expanded)
%              Number of leaves         :   54 (5392 expanded)
%              Depth                    :   23
%              Number of atoms          :  627 (45934 expanded)
%              Number of equality atoms :  212 (14851 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_157,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_177,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_90,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_94,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_139,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_147,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_139])).

tff(c_146,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_139])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_158,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_146,c_84])).

tff(c_15876,plain,(
    ! [A_1403,B_1404,C_1405] :
      ( k2_relset_1(A_1403,B_1404,C_1405) = k2_relat_1(C_1405)
      | ~ m1_subset_1(C_1405,k1_zfmisc_1(k2_zfmisc_1(A_1403,B_1404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15895,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_15876])).

tff(c_82,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_202,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_146,c_82])).

tff(c_15905,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15895,c_202])).

tff(c_74,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k2_struct_0(A_45))
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_15923,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15905,c_74])).

tff(c_15927,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15923])).

tff(c_15928,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_15927])).

tff(c_15423,plain,(
    ! [C_1335,A_1336,B_1337] :
      ( v1_relat_1(C_1335)
      | ~ m1_subset_1(C_1335,k1_zfmisc_1(k2_zfmisc_1(A_1336,B_1337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_15440,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_15423])).

tff(c_15547,plain,(
    ! [C_1353,A_1354,B_1355] :
      ( v4_relat_1(C_1353,A_1354)
      | ~ m1_subset_1(C_1353,k1_zfmisc_1(k2_zfmisc_1(A_1354,B_1355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15566,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_158,c_15547])).

tff(c_15839,plain,(
    ! [B_1400,A_1401] :
      ( k1_relat_1(B_1400) = A_1401
      | ~ v1_partfun1(B_1400,A_1401)
      | ~ v4_relat_1(B_1400,A_1401)
      | ~ v1_relat_1(B_1400) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_15848,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15566,c_15839])).

tff(c_15858,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15440,c_15848])).

tff(c_15875,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_15858])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_148,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86])).

tff(c_159,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_148])).

tff(c_15917,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15905,c_159])).

tff(c_15918,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15905,c_158])).

tff(c_16220,plain,(
    ! [C_1443,A_1444,B_1445] :
      ( v1_partfun1(C_1443,A_1444)
      | ~ v1_funct_2(C_1443,A_1444,B_1445)
      | ~ v1_funct_1(C_1443)
      | ~ m1_subset_1(C_1443,k1_zfmisc_1(k2_zfmisc_1(A_1444,B_1445)))
      | v1_xboole_0(B_1445) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16223,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15918,c_16220])).

tff(c_16240,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_15917,c_16223])).

tff(c_16242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15928,c_15875,c_16240])).

tff(c_16243,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15858])).

tff(c_16255,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16243,c_158])).

tff(c_44,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_relset_1(A_29,B_30,C_31) = k2_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16379,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16255,c_44])).

tff(c_16252,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16243,c_202])).

tff(c_16392,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16379,c_16252])).

tff(c_16254,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16243,c_159])).

tff(c_16401,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16392,c_16254])).

tff(c_16397,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16392,c_16379])).

tff(c_80,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_16398,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16392,c_16255])).

tff(c_17486,plain,(
    ! [A_1564,B_1565,C_1566] :
      ( k2_tops_2(A_1564,B_1565,C_1566) = k2_funct_1(C_1566)
      | ~ v2_funct_1(C_1566)
      | k2_relset_1(A_1564,B_1565,C_1566) != B_1565
      | ~ m1_subset_1(C_1566,k1_zfmisc_1(k2_zfmisc_1(A_1564,B_1565)))
      | ~ v1_funct_2(C_1566,A_1564,B_1565)
      | ~ v1_funct_1(C_1566) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_17489,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16398,c_17486])).

tff(c_17506,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16401,c_16397,c_80,c_17489])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_160,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_168,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_641,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_relset_1(A_137,B_138,C_139) = k2_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_660,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_641])).

tff(c_670,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_202])).

tff(c_687,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_74])).

tff(c_691,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_687])).

tff(c_692,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_691])).

tff(c_209,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_226,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_209])).

tff(c_399,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_418,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_158,c_399])).

tff(c_611,plain,(
    ! [B_134,A_135] :
      ( k1_relat_1(B_134) = A_135
      | ~ v1_partfun1(B_134,A_135)
      | ~ v4_relat_1(B_134,A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_620,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_418,c_611])).

tff(c_630,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_620])).

tff(c_640,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_630])).

tff(c_681,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_159])).

tff(c_682,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_158])).

tff(c_993,plain,(
    ! [C_178,A_179,B_180] :
      ( v1_partfun1(C_178,A_179)
      | ~ v1_funct_2(C_178,A_179,B_180)
      | ~ v1_funct_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | v1_xboole_0(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_996,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_682,c_993])).

tff(c_1013,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_681,c_996])).

tff(c_1015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_640,c_1013])).

tff(c_1016,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_1027,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_158])).

tff(c_1166,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_relset_1(A_187,B_188,C_189) = k2_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1184,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1027,c_1166])).

tff(c_1024,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_202])).

tff(c_1195,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1024])).

tff(c_1026,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_159])).

tff(c_1205,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1026])).

tff(c_1200,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1184])).

tff(c_1202,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1027])).

tff(c_2583,plain,(
    ! [A_334,B_335,C_336] :
      ( k2_tops_2(A_334,B_335,C_336) = k2_funct_1(C_336)
      | ~ v2_funct_1(C_336)
      | k2_relset_1(A_334,B_335,C_336) != B_335
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335)))
      | ~ v1_funct_2(C_336,A_334,B_335)
      | ~ v1_funct_1(C_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2586,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1202,c_2583])).

tff(c_2603,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1205,c_1200,c_80,c_2586])).

tff(c_78,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_207,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_147,c_146,c_146,c_147,c_147,c_146,c_146,c_78])).

tff(c_208,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_1023,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1016,c_208])).

tff(c_1381,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1195,c_1195,c_1023])).

tff(c_2607,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_1381])).

tff(c_2502,plain,(
    ! [C_325,B_326,A_327] :
      ( v1_funct_2(k2_funct_1(C_325),B_326,A_327)
      | k2_relset_1(A_327,B_326,C_325) != B_326
      | ~ v2_funct_1(C_325)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326)))
      | ~ v1_funct_2(C_325,A_327,B_326)
      | ~ v1_funct_1(C_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2505,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1202,c_2502])).

tff(c_2522,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1205,c_80,c_1200,c_2505])).

tff(c_2623,plain,(
    ! [C_339,B_340,A_341] :
      ( m1_subset_1(k2_funct_1(C_339),k1_zfmisc_1(k2_zfmisc_1(B_340,A_341)))
      | k2_relset_1(A_341,B_340,C_339) != B_340
      | ~ v2_funct_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_341,B_340)))
      | ~ v1_funct_2(C_339,A_341,B_340)
      | ~ v1_funct_1(C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_60,plain,(
    ! [B_37,A_36,C_38] :
      ( k1_xboole_0 = B_37
      | k1_relset_1(A_36,B_37,C_38) = A_36
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4120,plain,(
    ! [A_471,B_472,C_473] :
      ( k1_xboole_0 = A_471
      | k1_relset_1(B_472,A_471,k2_funct_1(C_473)) = B_472
      | ~ v1_funct_2(k2_funct_1(C_473),B_472,A_471)
      | k2_relset_1(A_471,B_472,C_473) != B_472
      | ~ v2_funct_1(C_473)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472)))
      | ~ v1_funct_2(C_473,A_471,B_472)
      | ~ v1_funct_1(C_473) ) ),
    inference(resolution,[status(thm)],[c_2623,c_60])).

tff(c_4126,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1202,c_4120])).

tff(c_4144,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1205,c_80,c_1200,c_2522,c_4126])).

tff(c_4145,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2607,c_4144])).

tff(c_167,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_158,c_160])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_201,plain,
    ( k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_167,c_4])).

tff(c_389,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_1022,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_389])).

tff(c_1203,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1022])).

tff(c_4161,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4145,c_1203])).

tff(c_4175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_14,c_4161])).

tff(c_4176,plain,(
    k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4204,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_xboole_0
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_10])).

tff(c_4267,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4204])).

tff(c_4188,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4176,c_158])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4268,plain,(
    ! [C_482,A_483,B_484] :
      ( v4_relat_1(C_482,A_483)
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(A_483,B_484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4402,plain,(
    ! [A_497,A_498,B_499] :
      ( v4_relat_1(A_497,A_498)
      | ~ r1_tarski(A_497,k2_zfmisc_1(A_498,B_499)) ) ),
    inference(resolution,[status(thm)],[c_20,c_4268])).

tff(c_4423,plain,(
    ! [A_500,B_501] : v4_relat_1(k2_zfmisc_1(A_500,B_501),A_500) ),
    inference(resolution,[status(thm)],[c_8,c_4402])).

tff(c_4429,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_4423])).

tff(c_4525,plain,(
    ! [B_518,A_519] :
      ( k1_relat_1(B_518) = A_519
      | ~ v1_partfun1(B_518,A_519)
      | ~ v4_relat_1(B_518,A_519)
      | ~ v1_relat_1(B_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4531,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4429,c_4525])).

tff(c_4547,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_4531])).

tff(c_4569,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4547])).

tff(c_4676,plain,(
    ! [A_530,B_531,C_532] :
      ( k2_relset_1(A_530,B_531,C_532) = k2_relat_1(C_532)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4725,plain,(
    ! [C_539] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_539) = k2_relat_1(C_539)
      | ~ m1_subset_1(C_539,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_4676])).

tff(c_4735,plain,
    ( k2_struct_0('#skF_2') = k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_202])).

tff(c_4750,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4188,c_4735])).

tff(c_4763,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4750,c_159])).

tff(c_4768,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4750,c_74])).

tff(c_4772,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4768])).

tff(c_4773,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4772])).

tff(c_4759,plain,(
    k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4750,c_4176])).

tff(c_5203,plain,(
    ! [C_575,A_576,B_577] :
      ( v1_partfun1(C_575,A_576)
      | ~ v1_funct_2(C_575,A_576,B_577)
      | ~ v1_funct_1(C_575)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_576,B_577)))
      | v1_xboole_0(B_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_5206,plain,(
    ! [C_575] :
      ( v1_partfun1(C_575,k2_struct_0('#skF_1'))
      | ~ v1_funct_2(C_575,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_575)
      | ~ m1_subset_1(C_575,k1_zfmisc_1('#skF_3'))
      | v1_xboole_0(k2_relat_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4759,c_5203])).

tff(c_5230,plain,(
    ! [C_578] :
      ( v1_partfun1(C_578,k2_struct_0('#skF_1'))
      | ~ v1_funct_2(C_578,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_578)
      | ~ m1_subset_1(C_578,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4773,c_5206])).

tff(c_5233,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4763,c_5230])).

tff(c_5236,plain,(
    v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4188,c_88,c_5233])).

tff(c_5238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4569,c_5236])).

tff(c_5239,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4547])).

tff(c_5247,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5239,c_4176])).

tff(c_9975,plain,(
    ! [A_937,B_938,C_939] :
      ( k2_relset_1(A_937,B_938,C_939) = k2_relat_1(C_939)
      | ~ m1_subset_1(C_939,k1_zfmisc_1(k2_zfmisc_1(A_937,B_938))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10024,plain,(
    ! [C_946] :
      ( k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_946) = k2_relat_1(C_946)
      | ~ m1_subset_1(C_946,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5247,c_9975])).

tff(c_5249,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5239,c_202])).

tff(c_10034,plain,
    ( k2_struct_0('#skF_2') = k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10024,c_5249])).

tff(c_10049,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4188,c_10034])).

tff(c_10058,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10049,c_5247])).

tff(c_5250,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5239,c_159])).

tff(c_10057,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10049,c_5250])).

tff(c_10187,plain,(
    ! [A_958,B_959,A_960] :
      ( k2_relset_1(A_958,B_959,A_960) = k2_relat_1(A_960)
      | ~ r1_tarski(A_960,k2_zfmisc_1(A_958,B_959)) ) ),
    inference(resolution,[status(thm)],[c_20,c_9975])).

tff(c_10207,plain,(
    ! [A_958,B_959] : k2_relset_1(A_958,B_959,k2_zfmisc_1(A_958,B_959)) = k2_relat_1(k2_zfmisc_1(A_958,B_959)) ),
    inference(resolution,[status(thm)],[c_8,c_10187])).

tff(c_11154,plain,(
    ! [A_1036,B_1037,C_1038] :
      ( k2_tops_2(A_1036,B_1037,C_1038) = k2_funct_1(C_1038)
      | ~ v2_funct_1(C_1038)
      | k2_relset_1(A_1036,B_1037,C_1038) != B_1037
      | ~ m1_subset_1(C_1038,k1_zfmisc_1(k2_zfmisc_1(A_1036,B_1037)))
      | ~ v1_funct_2(C_1038,A_1036,B_1037)
      | ~ v1_funct_1(C_1038) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_12381,plain,(
    ! [A_1133,B_1134,A_1135] :
      ( k2_tops_2(A_1133,B_1134,A_1135) = k2_funct_1(A_1135)
      | ~ v2_funct_1(A_1135)
      | k2_relset_1(A_1133,B_1134,A_1135) != B_1134
      | ~ v1_funct_2(A_1135,A_1133,B_1134)
      | ~ v1_funct_1(A_1135)
      | ~ r1_tarski(A_1135,k2_zfmisc_1(A_1133,B_1134)) ) ),
    inference(resolution,[status(thm)],[c_20,c_11154])).

tff(c_12398,plain,(
    ! [A_1133,B_1134] :
      ( k2_tops_2(A_1133,B_1134,k2_zfmisc_1(A_1133,B_1134)) = k2_funct_1(k2_zfmisc_1(A_1133,B_1134))
      | ~ v2_funct_1(k2_zfmisc_1(A_1133,B_1134))
      | k2_relset_1(A_1133,B_1134,k2_zfmisc_1(A_1133,B_1134)) != B_1134
      | ~ v1_funct_2(k2_zfmisc_1(A_1133,B_1134),A_1133,B_1134)
      | ~ v1_funct_1(k2_zfmisc_1(A_1133,B_1134)) ) ),
    inference(resolution,[status(thm)],[c_8,c_12381])).

tff(c_13774,plain,(
    ! [A_1245,B_1246] :
      ( k2_tops_2(A_1245,B_1246,k2_zfmisc_1(A_1245,B_1246)) = k2_funct_1(k2_zfmisc_1(A_1245,B_1246))
      | ~ v2_funct_1(k2_zfmisc_1(A_1245,B_1246))
      | k2_relat_1(k2_zfmisc_1(A_1245,B_1246)) != B_1246
      | ~ v1_funct_2(k2_zfmisc_1(A_1245,B_1246),A_1245,B_1246)
      | ~ v1_funct_1(k2_zfmisc_1(A_1245,B_1246)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10207,c_12398])).

tff(c_13792,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))) = k2_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v2_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))
    | k2_relat_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))) != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10058,c_13774])).

tff(c_13810,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10058,c_10057,c_10058,c_80,c_10058,c_10058,c_10058,c_13792])).

tff(c_5248,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5239,c_5239,c_208])).

tff(c_10056,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10049,c_10049,c_10049,c_5248])).

tff(c_13835,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13810,c_10056])).

tff(c_11034,plain,(
    ! [C_1021,B_1022,A_1023] :
      ( v1_funct_2(k2_funct_1(C_1021),B_1022,A_1023)
      | k2_relset_1(A_1023,B_1022,C_1021) != B_1022
      | ~ v2_funct_1(C_1021)
      | ~ m1_subset_1(C_1021,k1_zfmisc_1(k2_zfmisc_1(A_1023,B_1022)))
      | ~ v1_funct_2(C_1021,A_1023,B_1022)
      | ~ v1_funct_1(C_1021) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_11052,plain,(
    ! [A_6,B_1022,A_1023] :
      ( v1_funct_2(k2_funct_1(A_6),B_1022,A_1023)
      | k2_relset_1(A_1023,B_1022,A_6) != B_1022
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_2(A_6,A_1023,B_1022)
      | ~ v1_funct_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_1023,B_1022)) ) ),
    inference(resolution,[status(thm)],[c_20,c_11034])).

tff(c_11383,plain,(
    ! [C_1051,B_1052,A_1053] :
      ( m1_subset_1(k2_funct_1(C_1051),k1_zfmisc_1(k2_zfmisc_1(B_1052,A_1053)))
      | k2_relset_1(A_1053,B_1052,C_1051) != B_1052
      | ~ v2_funct_1(C_1051)
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(k2_zfmisc_1(A_1053,B_1052)))
      | ~ v1_funct_2(C_1051,A_1053,B_1052)
      | ~ v1_funct_1(C_1051) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_12955,plain,(
    ! [A_1174,B_1175,C_1176] :
      ( k1_xboole_0 = A_1174
      | k1_relset_1(B_1175,A_1174,k2_funct_1(C_1176)) = B_1175
      | ~ v1_funct_2(k2_funct_1(C_1176),B_1175,A_1174)
      | k2_relset_1(A_1174,B_1175,C_1176) != B_1175
      | ~ v2_funct_1(C_1176)
      | ~ m1_subset_1(C_1176,k1_zfmisc_1(k2_zfmisc_1(A_1174,B_1175)))
      | ~ v1_funct_2(C_1176,A_1174,B_1175)
      | ~ v1_funct_1(C_1176) ) ),
    inference(resolution,[status(thm)],[c_11383,c_60])).

tff(c_14392,plain,(
    ! [A_1287,B_1288,A_1289] :
      ( k1_xboole_0 = A_1287
      | k1_relset_1(B_1288,A_1287,k2_funct_1(A_1289)) = B_1288
      | ~ v1_funct_2(k2_funct_1(A_1289),B_1288,A_1287)
      | k2_relset_1(A_1287,B_1288,A_1289) != B_1288
      | ~ v2_funct_1(A_1289)
      | ~ v1_funct_2(A_1289,A_1287,B_1288)
      | ~ v1_funct_1(A_1289)
      | ~ r1_tarski(A_1289,k2_zfmisc_1(A_1287,B_1288)) ) ),
    inference(resolution,[status(thm)],[c_20,c_12955])).

tff(c_14437,plain,(
    ! [A_1290,B_1291,A_1292] :
      ( k1_xboole_0 = A_1290
      | k1_relset_1(B_1291,A_1290,k2_funct_1(A_1292)) = B_1291
      | k2_relset_1(A_1290,B_1291,A_1292) != B_1291
      | ~ v2_funct_1(A_1292)
      | ~ v1_funct_2(A_1292,A_1290,B_1291)
      | ~ v1_funct_1(A_1292)
      | ~ r1_tarski(A_1292,k2_zfmisc_1(A_1290,B_1291)) ) ),
    inference(resolution,[status(thm)],[c_11052,c_14392])).

tff(c_14457,plain,(
    ! [A_1290,B_1291] :
      ( k1_xboole_0 = A_1290
      | k1_relset_1(B_1291,A_1290,k2_funct_1(k2_zfmisc_1(A_1290,B_1291))) = B_1291
      | k2_relset_1(A_1290,B_1291,k2_zfmisc_1(A_1290,B_1291)) != B_1291
      | ~ v2_funct_1(k2_zfmisc_1(A_1290,B_1291))
      | ~ v1_funct_2(k2_zfmisc_1(A_1290,B_1291),A_1290,B_1291)
      | ~ v1_funct_1(k2_zfmisc_1(A_1290,B_1291)) ) ),
    inference(resolution,[status(thm)],[c_8,c_14437])).

tff(c_14466,plain,(
    ! [A_1293,B_1294] :
      ( k1_xboole_0 = A_1293
      | k1_relset_1(B_1294,A_1293,k2_funct_1(k2_zfmisc_1(A_1293,B_1294))) = B_1294
      | k2_relat_1(k2_zfmisc_1(A_1293,B_1294)) != B_1294
      | ~ v2_funct_1(k2_zfmisc_1(A_1293,B_1294))
      | ~ v1_funct_2(k2_zfmisc_1(A_1293,B_1294),A_1293,B_1294)
      | ~ v1_funct_1(k2_zfmisc_1(A_1293,B_1294)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10207,c_14457])).

tff(c_14518,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | k2_relat_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_funct_2(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10058,c_14466])).

tff(c_14551,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10058,c_10057,c_10058,c_80,c_10058,c_10058,c_14518])).

tff(c_14552,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_13835,c_14551])).

tff(c_4288,plain,(
    ! [C_485] :
      ( v4_relat_1(C_485,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(C_485,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4176,c_4268])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4360,plain,(
    ! [C_494] :
      ( k7_relat_1(C_494,k2_struct_0('#skF_1')) = C_494
      | ~ v1_relat_1(C_494)
      | ~ m1_subset_1(C_494,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4288,c_30])).

tff(c_4363,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4188,c_4360])).

tff(c_4374,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_4363])).

tff(c_5244,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5239,c_4374])).

tff(c_14617,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14552,c_5244])).

tff(c_14612,plain,(
    k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14552,c_10058])).

tff(c_26,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4426,plain,(
    ! [A_500,B_501] :
      ( k7_relat_1(k2_zfmisc_1(A_500,B_501),A_500) = k2_zfmisc_1(A_500,B_501)
      | ~ v1_relat_1(k2_zfmisc_1(A_500,B_501)) ) ),
    inference(resolution,[status(thm)],[c_4423,c_30])).

tff(c_4438,plain,(
    ! [A_500,B_501] : k7_relat_1(k2_zfmisc_1(A_500,B_501),A_500) = k2_zfmisc_1(A_500,B_501) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4426])).

tff(c_14966,plain,(
    k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3')) = k7_relat_1('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14612,c_4438])).

tff(c_15049,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14617,c_14,c_14966])).

tff(c_15051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4267,c_15049])).

tff(c_15053,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4204])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_15069,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15053,c_2])).

tff(c_15052,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4204])).

tff(c_15269,plain,
    ( k2_struct_0('#skF_1') = '#skF_3'
    | k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15053,c_15053,c_15052])).

tff(c_15270,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_15269])).

tff(c_15282,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15270,c_74])).

tff(c_15286,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_15069,c_15282])).

tff(c_15288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_15286])).

tff(c_15290,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15269])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15068,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15053,c_15053,c_32])).

tff(c_15066,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15053,c_16])).

tff(c_15400,plain,(
    ! [A_1332,B_1333,C_1334] :
      ( k2_relset_1(A_1332,B_1333,C_1334) = k2_relat_1(C_1334)
      | ~ m1_subset_1(C_1334,k1_zfmisc_1(k2_zfmisc_1(A_1332,B_1333))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15404,plain,(
    ! [A_1332,B_1333] : k2_relset_1(A_1332,B_1333,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15066,c_15400])).

tff(c_15416,plain,(
    ! [A_1332,B_1333] : k2_relset_1(A_1332,B_1333,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15068,c_15404])).

tff(c_15289,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15269])).

tff(c_15294,plain,(
    k2_relset_1('#skF_3',k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15289,c_202])).

tff(c_15418,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15416,c_15294])).

tff(c_15420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15290,c_15418])).

tff(c_15421,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_16251,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16243,c_16243,c_16243,c_15421])).

tff(c_16612,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16392,c_16392,c_16251])).

tff(c_17511,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17506,c_16612])).

tff(c_17003,plain,(
    ! [C_1514,A_1515,B_1516] :
      ( v1_funct_1(k2_funct_1(C_1514))
      | k2_relset_1(A_1515,B_1516,C_1514) != B_1516
      | ~ v2_funct_1(C_1514)
      | ~ m1_subset_1(C_1514,k1_zfmisc_1(k2_zfmisc_1(A_1515,B_1516)))
      | ~ v1_funct_2(C_1514,A_1515,B_1516)
      | ~ v1_funct_1(C_1514) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_17006,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16398,c_17003])).

tff(c_17023,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16401,c_80,c_16397,c_17006])).

tff(c_15577,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15566,c_30])).

tff(c_15580,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15440,c_15577])).

tff(c_16248,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16243,c_15580])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16293,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16248,c_28])).

tff(c_16297,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15440,c_16293])).

tff(c_16854,plain,(
    ! [A_1503,B_1504] :
      ( k9_relat_1(k2_funct_1(A_1503),k9_relat_1(A_1503,B_1504)) = B_1504
      | ~ r1_tarski(B_1504,k1_relat_1(A_1503))
      | ~ v2_funct_1(A_1503)
      | ~ v1_funct_1(A_1503)
      | ~ v1_relat_1(A_1503) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16869,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16297,c_16854])).

tff(c_16879,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15440,c_88,c_80,c_8,c_16869])).

tff(c_36,plain,(
    ! [A_20,B_22] :
      ( k9_relat_1(k2_funct_1(A_20),k9_relat_1(A_20,B_22)) = B_22
      | ~ r1_tarski(B_22,k1_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16887,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16879,c_36])).

tff(c_17048,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17023,c_16887])).

tff(c_17049,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17048])).

tff(c_17228,plain,(
    ! [C_1541,B_1542,A_1543] :
      ( m1_subset_1(k2_funct_1(C_1541),k1_zfmisc_1(k2_zfmisc_1(B_1542,A_1543)))
      | k2_relset_1(A_1543,B_1542,C_1541) != B_1542
      | ~ v2_funct_1(C_1541)
      | ~ m1_subset_1(C_1541,k1_zfmisc_1(k2_zfmisc_1(A_1543,B_1542)))
      | ~ v1_funct_2(C_1541,A_1543,B_1542)
      | ~ v1_funct_1(C_1541) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_24,plain,(
    ! [B_13,A_11] :
      ( v1_relat_1(B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_17260,plain,(
    ! [C_1541,B_1542,A_1543] :
      ( v1_relat_1(k2_funct_1(C_1541))
      | ~ v1_relat_1(k2_zfmisc_1(B_1542,A_1543))
      | k2_relset_1(A_1543,B_1542,C_1541) != B_1542
      | ~ v2_funct_1(C_1541)
      | ~ m1_subset_1(C_1541,k1_zfmisc_1(k2_zfmisc_1(A_1543,B_1542)))
      | ~ v1_funct_2(C_1541,A_1543,B_1542)
      | ~ v1_funct_1(C_1541) ) ),
    inference(resolution,[status(thm)],[c_17228,c_24])).

tff(c_17349,plain,(
    ! [C_1548,A_1549,B_1550] :
      ( v1_relat_1(k2_funct_1(C_1548))
      | k2_relset_1(A_1549,B_1550,C_1548) != B_1550
      | ~ v2_funct_1(C_1548)
      | ~ m1_subset_1(C_1548,k1_zfmisc_1(k2_zfmisc_1(A_1549,B_1550)))
      | ~ v1_funct_2(C_1548,A_1549,B_1550)
      | ~ v1_funct_1(C_1548) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_17260])).

tff(c_17355,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16398,c_17349])).

tff(c_17373,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16401,c_80,c_16397,c_17355])).

tff(c_17375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17049,c_17373])).

tff(c_17377,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17048])).

tff(c_17532,plain,(
    ! [C_1570,B_1571,A_1572] :
      ( m1_subset_1(k2_funct_1(C_1570),k1_zfmisc_1(k2_zfmisc_1(B_1571,A_1572)))
      | k2_relset_1(A_1572,B_1571,C_1570) != B_1571
      | ~ v2_funct_1(C_1570)
      | ~ m1_subset_1(C_1570,k1_zfmisc_1(k2_zfmisc_1(A_1572,B_1571)))
      | ~ v1_funct_2(C_1570,A_1572,B_1571)
      | ~ v1_funct_1(C_1570) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    ! [C_28,A_26,B_27] :
      ( v4_relat_1(C_28,A_26)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_17985,plain,(
    ! [C_1611,B_1612,A_1613] :
      ( v4_relat_1(k2_funct_1(C_1611),B_1612)
      | k2_relset_1(A_1613,B_1612,C_1611) != B_1612
      | ~ v2_funct_1(C_1611)
      | ~ m1_subset_1(C_1611,k1_zfmisc_1(k2_zfmisc_1(A_1613,B_1612)))
      | ~ v1_funct_2(C_1611,A_1613,B_1612)
      | ~ v1_funct_1(C_1611) ) ),
    inference(resolution,[status(thm)],[c_17532,c_42])).

tff(c_17991,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16398,c_17985])).

tff(c_18009,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16401,c_80,c_16397,c_17991])).

tff(c_18018,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18009,c_30])).

tff(c_18024,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17377,c_18018])).

tff(c_18028,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18024,c_28])).

tff(c_18032,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17377,c_16879,c_18028])).

tff(c_18666,plain,(
    ! [B_1663,A_1664,C_1665] :
      ( k2_relset_1(B_1663,A_1664,k2_funct_1(C_1665)) = k2_relat_1(k2_funct_1(C_1665))
      | k2_relset_1(A_1664,B_1663,C_1665) != B_1663
      | ~ v2_funct_1(C_1665)
      | ~ m1_subset_1(C_1665,k1_zfmisc_1(k2_zfmisc_1(A_1664,B_1663)))
      | ~ v1_funct_2(C_1665,A_1664,B_1663)
      | ~ v1_funct_1(C_1665) ) ),
    inference(resolution,[status(thm)],[c_17532,c_44])).

tff(c_18672,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16398,c_18666])).

tff(c_18690,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16401,c_80,c_16397,c_18032,c_18672])).

tff(c_18692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17511,c_18690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:18:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.36/4.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/4.47  
% 11.53/4.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/4.47  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.53/4.47  
% 11.53/4.47  %Foreground sorts:
% 11.53/4.47  
% 11.53/4.47  
% 11.53/4.47  %Background operators:
% 11.53/4.47  
% 11.53/4.47  
% 11.53/4.47  %Foreground operators:
% 11.53/4.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.53/4.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.53/4.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.53/4.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.53/4.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.53/4.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.53/4.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.53/4.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.53/4.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.53/4.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.53/4.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.53/4.47  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 11.53/4.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.53/4.47  tff('#skF_2', type, '#skF_2': $i).
% 11.53/4.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.53/4.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.53/4.47  tff('#skF_3', type, '#skF_3': $i).
% 11.53/4.47  tff('#skF_1', type, '#skF_1': $i).
% 11.53/4.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.53/4.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.53/4.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.53/4.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.53/4.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.53/4.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.53/4.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.53/4.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.53/4.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.53/4.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.53/4.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.53/4.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.53/4.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.53/4.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.53/4.47  
% 11.74/4.51  tff(f_201, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 11.74/4.51  tff(f_157, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 11.74/4.51  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.74/4.51  tff(f_165, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 11.74/4.51  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.74/4.51  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.74/4.51  tff(f_137, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 11.74/4.51  tff(f_111, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 11.74/4.51  tff(f_177, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 11.74/4.51  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.74/4.51  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.74/4.51  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.74/4.51  tff(f_153, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.74/4.51  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.74/4.51  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.74/4.51  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 11.74/4.51  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.74/4.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.74/4.51  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 11.74/4.51  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 11.74/4.51  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 11.74/4.51  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.74/4.51  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_92, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_90, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_94, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_139, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.74/4.51  tff(c_147, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_94, c_139])).
% 11.74/4.51  tff(c_146, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_139])).
% 11.74/4.51  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_158, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_146, c_84])).
% 11.74/4.51  tff(c_15876, plain, (![A_1403, B_1404, C_1405]: (k2_relset_1(A_1403, B_1404, C_1405)=k2_relat_1(C_1405) | ~m1_subset_1(C_1405, k1_zfmisc_1(k2_zfmisc_1(A_1403, B_1404))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.74/4.51  tff(c_15895, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_158, c_15876])).
% 11.74/4.51  tff(c_82, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_202, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_146, c_82])).
% 11.74/4.51  tff(c_15905, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15895, c_202])).
% 11.74/4.51  tff(c_74, plain, (![A_45]: (~v1_xboole_0(k2_struct_0(A_45)) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_165])).
% 11.74/4.51  tff(c_15923, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15905, c_74])).
% 11.74/4.51  tff(c_15927, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15923])).
% 11.74/4.51  tff(c_15928, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_15927])).
% 11.74/4.51  tff(c_15423, plain, (![C_1335, A_1336, B_1337]: (v1_relat_1(C_1335) | ~m1_subset_1(C_1335, k1_zfmisc_1(k2_zfmisc_1(A_1336, B_1337))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.74/4.51  tff(c_15440, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_158, c_15423])).
% 11.74/4.51  tff(c_15547, plain, (![C_1353, A_1354, B_1355]: (v4_relat_1(C_1353, A_1354) | ~m1_subset_1(C_1353, k1_zfmisc_1(k2_zfmisc_1(A_1354, B_1355))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.74/4.51  tff(c_15566, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_158, c_15547])).
% 11.74/4.51  tff(c_15839, plain, (![B_1400, A_1401]: (k1_relat_1(B_1400)=A_1401 | ~v1_partfun1(B_1400, A_1401) | ~v4_relat_1(B_1400, A_1401) | ~v1_relat_1(B_1400))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.74/4.51  tff(c_15848, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_15566, c_15839])).
% 11.74/4.51  tff(c_15858, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15440, c_15848])).
% 11.74/4.51  tff(c_15875, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_15858])).
% 11.74/4.51  tff(c_86, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_148, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86])).
% 11.74/4.51  tff(c_159, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_148])).
% 11.74/4.51  tff(c_15917, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15905, c_159])).
% 11.74/4.51  tff(c_15918, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_15905, c_158])).
% 11.74/4.51  tff(c_16220, plain, (![C_1443, A_1444, B_1445]: (v1_partfun1(C_1443, A_1444) | ~v1_funct_2(C_1443, A_1444, B_1445) | ~v1_funct_1(C_1443) | ~m1_subset_1(C_1443, k1_zfmisc_1(k2_zfmisc_1(A_1444, B_1445))) | v1_xboole_0(B_1445))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.74/4.51  tff(c_16223, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15918, c_16220])).
% 11.74/4.51  tff(c_16240, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_15917, c_16223])).
% 11.74/4.51  tff(c_16242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15928, c_15875, c_16240])).
% 11.74/4.51  tff(c_16243, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_15858])).
% 11.74/4.51  tff(c_16255, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_16243, c_158])).
% 11.74/4.51  tff(c_44, plain, (![A_29, B_30, C_31]: (k2_relset_1(A_29, B_30, C_31)=k2_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.74/4.51  tff(c_16379, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16255, c_44])).
% 11.74/4.51  tff(c_16252, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16243, c_202])).
% 11.74/4.51  tff(c_16392, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16379, c_16252])).
% 11.74/4.51  tff(c_16254, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16243, c_159])).
% 11.74/4.51  tff(c_16401, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16392, c_16254])).
% 11.74/4.51  tff(c_16397, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16392, c_16379])).
% 11.74/4.51  tff(c_80, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_16398, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_16392, c_16255])).
% 11.74/4.51  tff(c_17486, plain, (![A_1564, B_1565, C_1566]: (k2_tops_2(A_1564, B_1565, C_1566)=k2_funct_1(C_1566) | ~v2_funct_1(C_1566) | k2_relset_1(A_1564, B_1565, C_1566)!=B_1565 | ~m1_subset_1(C_1566, k1_zfmisc_1(k2_zfmisc_1(A_1564, B_1565))) | ~v1_funct_2(C_1566, A_1564, B_1565) | ~v1_funct_1(C_1566))), inference(cnfTransformation, [status(thm)], [f_177])).
% 11.74/4.51  tff(c_17489, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16398, c_17486])).
% 11.74/4.51  tff(c_17506, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16401, c_16397, c_80, c_17489])).
% 11.74/4.51  tff(c_16, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.74/4.51  tff(c_160, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.74/4.51  tff(c_168, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_16, c_160])).
% 11.74/4.51  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.74/4.51  tff(c_641, plain, (![A_137, B_138, C_139]: (k2_relset_1(A_137, B_138, C_139)=k2_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.74/4.51  tff(c_660, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_158, c_641])).
% 11.74/4.51  tff(c_670, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_660, c_202])).
% 11.74/4.51  tff(c_687, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_670, c_74])).
% 11.74/4.51  tff(c_691, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_687])).
% 11.74/4.51  tff(c_692, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_691])).
% 11.74/4.51  tff(c_209, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.74/4.51  tff(c_226, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_158, c_209])).
% 11.74/4.51  tff(c_399, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.74/4.51  tff(c_418, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_158, c_399])).
% 11.74/4.51  tff(c_611, plain, (![B_134, A_135]: (k1_relat_1(B_134)=A_135 | ~v1_partfun1(B_134, A_135) | ~v4_relat_1(B_134, A_135) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.74/4.51  tff(c_620, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_418, c_611])).
% 11.74/4.51  tff(c_630, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_620])).
% 11.74/4.51  tff(c_640, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_630])).
% 11.74/4.51  tff(c_681, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_159])).
% 11.74/4.51  tff(c_682, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_158])).
% 11.74/4.51  tff(c_993, plain, (![C_178, A_179, B_180]: (v1_partfun1(C_178, A_179) | ~v1_funct_2(C_178, A_179, B_180) | ~v1_funct_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | v1_xboole_0(B_180))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.74/4.51  tff(c_996, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_682, c_993])).
% 11.74/4.51  tff(c_1013, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_681, c_996])).
% 11.74/4.51  tff(c_1015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_692, c_640, c_1013])).
% 11.74/4.51  tff(c_1016, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_630])).
% 11.74/4.51  tff(c_1027, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_158])).
% 11.74/4.51  tff(c_1166, plain, (![A_187, B_188, C_189]: (k2_relset_1(A_187, B_188, C_189)=k2_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.74/4.51  tff(c_1184, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1027, c_1166])).
% 11.74/4.51  tff(c_1024, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_202])).
% 11.74/4.51  tff(c_1195, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1024])).
% 11.74/4.51  tff(c_1026, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_159])).
% 11.74/4.51  tff(c_1205, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1026])).
% 11.74/4.51  tff(c_1200, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1184])).
% 11.74/4.51  tff(c_1202, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1027])).
% 11.74/4.51  tff(c_2583, plain, (![A_334, B_335, C_336]: (k2_tops_2(A_334, B_335, C_336)=k2_funct_1(C_336) | ~v2_funct_1(C_336) | k2_relset_1(A_334, B_335, C_336)!=B_335 | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))) | ~v1_funct_2(C_336, A_334, B_335) | ~v1_funct_1(C_336))), inference(cnfTransformation, [status(thm)], [f_177])).
% 11.74/4.51  tff(c_2586, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1202, c_2583])).
% 11.74/4.51  tff(c_2603, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1205, c_1200, c_80, c_2586])).
% 11.74/4.51  tff(c_78, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.74/4.51  tff(c_207, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_147, c_146, c_146, c_147, c_147, c_146, c_146, c_78])).
% 11.74/4.51  tff(c_208, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_207])).
% 11.74/4.51  tff(c_1023, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1016, c_208])).
% 11.74/4.51  tff(c_1381, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1195, c_1195, c_1023])).
% 11.74/4.51  tff(c_2607, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2603, c_1381])).
% 11.74/4.51  tff(c_2502, plain, (![C_325, B_326, A_327]: (v1_funct_2(k2_funct_1(C_325), B_326, A_327) | k2_relset_1(A_327, B_326, C_325)!=B_326 | ~v2_funct_1(C_325) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))) | ~v1_funct_2(C_325, A_327, B_326) | ~v1_funct_1(C_325))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.74/4.51  tff(c_2505, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1202, c_2502])).
% 11.74/4.51  tff(c_2522, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1205, c_80, c_1200, c_2505])).
% 11.74/4.51  tff(c_2623, plain, (![C_339, B_340, A_341]: (m1_subset_1(k2_funct_1(C_339), k1_zfmisc_1(k2_zfmisc_1(B_340, A_341))) | k2_relset_1(A_341, B_340, C_339)!=B_340 | ~v2_funct_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_341, B_340))) | ~v1_funct_2(C_339, A_341, B_340) | ~v1_funct_1(C_339))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.74/4.51  tff(c_60, plain, (![B_37, A_36, C_38]: (k1_xboole_0=B_37 | k1_relset_1(A_36, B_37, C_38)=A_36 | ~v1_funct_2(C_38, A_36, B_37) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.74/4.51  tff(c_4120, plain, (![A_471, B_472, C_473]: (k1_xboole_0=A_471 | k1_relset_1(B_472, A_471, k2_funct_1(C_473))=B_472 | ~v1_funct_2(k2_funct_1(C_473), B_472, A_471) | k2_relset_1(A_471, B_472, C_473)!=B_472 | ~v2_funct_1(C_473) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_471, B_472))) | ~v1_funct_2(C_473, A_471, B_472) | ~v1_funct_1(C_473))), inference(resolution, [status(thm)], [c_2623, c_60])).
% 11.74/4.51  tff(c_4126, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1202, c_4120])).
% 11.74/4.51  tff(c_4144, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1205, c_80, c_1200, c_2522, c_4126])).
% 11.74/4.51  tff(c_4145, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2607, c_4144])).
% 11.74/4.51  tff(c_167, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_158, c_160])).
% 11.74/4.51  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.74/4.51  tff(c_201, plain, (k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))='#skF_3' | ~r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')), '#skF_3')), inference(resolution, [status(thm)], [c_167, c_4])).
% 11.74/4.51  tff(c_389, plain, (~r1_tarski(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_201])).
% 11.74/4.51  tff(c_1022, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_389])).
% 11.74/4.51  tff(c_1203, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1022])).
% 11.74/4.51  tff(c_4161, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4145, c_1203])).
% 11.74/4.51  tff(c_4175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_14, c_4161])).
% 11.74/4.51  tff(c_4176, plain, (k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))='#skF_3'), inference(splitRight, [status(thm)], [c_201])).
% 11.74/4.51  tff(c_10, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.74/4.51  tff(c_4204, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_xboole_0 | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4176, c_10])).
% 11.74/4.51  tff(c_4267, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4204])).
% 11.74/4.51  tff(c_4188, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4176, c_158])).
% 11.74/4.51  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.74/4.51  tff(c_20, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.74/4.51  tff(c_4268, plain, (![C_482, A_483, B_484]: (v4_relat_1(C_482, A_483) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(A_483, B_484))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.74/4.51  tff(c_4402, plain, (![A_497, A_498, B_499]: (v4_relat_1(A_497, A_498) | ~r1_tarski(A_497, k2_zfmisc_1(A_498, B_499)))), inference(resolution, [status(thm)], [c_20, c_4268])).
% 11.74/4.51  tff(c_4423, plain, (![A_500, B_501]: (v4_relat_1(k2_zfmisc_1(A_500, B_501), A_500))), inference(resolution, [status(thm)], [c_8, c_4402])).
% 11.74/4.51  tff(c_4429, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4176, c_4423])).
% 11.74/4.51  tff(c_4525, plain, (![B_518, A_519]: (k1_relat_1(B_518)=A_519 | ~v1_partfun1(B_518, A_519) | ~v4_relat_1(B_518, A_519) | ~v1_relat_1(B_518))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.74/4.51  tff(c_4531, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4429, c_4525])).
% 11.74/4.51  tff(c_4547, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_4531])).
% 11.74/4.51  tff(c_4569, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_4547])).
% 11.74/4.51  tff(c_4676, plain, (![A_530, B_531, C_532]: (k2_relset_1(A_530, B_531, C_532)=k2_relat_1(C_532) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.74/4.51  tff(c_4725, plain, (![C_539]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_539)=k2_relat_1(C_539) | ~m1_subset_1(C_539, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4176, c_4676])).
% 11.74/4.51  tff(c_4735, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_202])).
% 11.74/4.51  tff(c_4750, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4188, c_4735])).
% 11.74/4.51  tff(c_4763, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4750, c_159])).
% 11.74/4.51  tff(c_4768, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4750, c_74])).
% 11.74/4.51  tff(c_4772, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_4768])).
% 11.74/4.51  tff(c_4773, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_4772])).
% 11.74/4.51  tff(c_4759, plain, (k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4750, c_4176])).
% 11.74/4.51  tff(c_5203, plain, (![C_575, A_576, B_577]: (v1_partfun1(C_575, A_576) | ~v1_funct_2(C_575, A_576, B_577) | ~v1_funct_1(C_575) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_576, B_577))) | v1_xboole_0(B_577))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.74/4.51  tff(c_5206, plain, (![C_575]: (v1_partfun1(C_575, k2_struct_0('#skF_1')) | ~v1_funct_2(C_575, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_575) | ~m1_subset_1(C_575, k1_zfmisc_1('#skF_3')) | v1_xboole_0(k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4759, c_5203])).
% 11.74/4.51  tff(c_5230, plain, (![C_578]: (v1_partfun1(C_578, k2_struct_0('#skF_1')) | ~v1_funct_2(C_578, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_578) | ~m1_subset_1(C_578, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_4773, c_5206])).
% 11.74/4.51  tff(c_5233, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_4763, c_5230])).
% 11.74/4.51  tff(c_5236, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4188, c_88, c_5233])).
% 11.74/4.51  tff(c_5238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4569, c_5236])).
% 11.74/4.51  tff(c_5239, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_4547])).
% 11.74/4.51  tff(c_5247, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5239, c_4176])).
% 11.74/4.51  tff(c_9975, plain, (![A_937, B_938, C_939]: (k2_relset_1(A_937, B_938, C_939)=k2_relat_1(C_939) | ~m1_subset_1(C_939, k1_zfmisc_1(k2_zfmisc_1(A_937, B_938))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.74/4.51  tff(c_10024, plain, (![C_946]: (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_946)=k2_relat_1(C_946) | ~m1_subset_1(C_946, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5247, c_9975])).
% 11.74/4.51  tff(c_5249, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5239, c_202])).
% 11.74/4.51  tff(c_10034, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10024, c_5249])).
% 11.74/4.51  tff(c_10049, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4188, c_10034])).
% 11.74/4.51  tff(c_10058, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10049, c_5247])).
% 11.74/4.51  tff(c_5250, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5239, c_159])).
% 11.74/4.51  tff(c_10057, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10049, c_5250])).
% 11.74/4.51  tff(c_10187, plain, (![A_958, B_959, A_960]: (k2_relset_1(A_958, B_959, A_960)=k2_relat_1(A_960) | ~r1_tarski(A_960, k2_zfmisc_1(A_958, B_959)))), inference(resolution, [status(thm)], [c_20, c_9975])).
% 11.74/4.51  tff(c_10207, plain, (![A_958, B_959]: (k2_relset_1(A_958, B_959, k2_zfmisc_1(A_958, B_959))=k2_relat_1(k2_zfmisc_1(A_958, B_959)))), inference(resolution, [status(thm)], [c_8, c_10187])).
% 11.74/4.51  tff(c_11154, plain, (![A_1036, B_1037, C_1038]: (k2_tops_2(A_1036, B_1037, C_1038)=k2_funct_1(C_1038) | ~v2_funct_1(C_1038) | k2_relset_1(A_1036, B_1037, C_1038)!=B_1037 | ~m1_subset_1(C_1038, k1_zfmisc_1(k2_zfmisc_1(A_1036, B_1037))) | ~v1_funct_2(C_1038, A_1036, B_1037) | ~v1_funct_1(C_1038))), inference(cnfTransformation, [status(thm)], [f_177])).
% 11.74/4.51  tff(c_12381, plain, (![A_1133, B_1134, A_1135]: (k2_tops_2(A_1133, B_1134, A_1135)=k2_funct_1(A_1135) | ~v2_funct_1(A_1135) | k2_relset_1(A_1133, B_1134, A_1135)!=B_1134 | ~v1_funct_2(A_1135, A_1133, B_1134) | ~v1_funct_1(A_1135) | ~r1_tarski(A_1135, k2_zfmisc_1(A_1133, B_1134)))), inference(resolution, [status(thm)], [c_20, c_11154])).
% 11.74/4.51  tff(c_12398, plain, (![A_1133, B_1134]: (k2_tops_2(A_1133, B_1134, k2_zfmisc_1(A_1133, B_1134))=k2_funct_1(k2_zfmisc_1(A_1133, B_1134)) | ~v2_funct_1(k2_zfmisc_1(A_1133, B_1134)) | k2_relset_1(A_1133, B_1134, k2_zfmisc_1(A_1133, B_1134))!=B_1134 | ~v1_funct_2(k2_zfmisc_1(A_1133, B_1134), A_1133, B_1134) | ~v1_funct_1(k2_zfmisc_1(A_1133, B_1134)))), inference(resolution, [status(thm)], [c_8, c_12381])).
% 11.74/4.51  tff(c_13774, plain, (![A_1245, B_1246]: (k2_tops_2(A_1245, B_1246, k2_zfmisc_1(A_1245, B_1246))=k2_funct_1(k2_zfmisc_1(A_1245, B_1246)) | ~v2_funct_1(k2_zfmisc_1(A_1245, B_1246)) | k2_relat_1(k2_zfmisc_1(A_1245, B_1246))!=B_1246 | ~v1_funct_2(k2_zfmisc_1(A_1245, B_1246), A_1245, B_1246) | ~v1_funct_1(k2_zfmisc_1(A_1245, B_1246)))), inference(demodulation, [status(thm), theory('equality')], [c_10207, c_12398])).
% 11.74/4.51  tff(c_13792, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))=k2_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v2_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))) | k2_relat_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10058, c_13774])).
% 11.74/4.51  tff(c_13810, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10058, c_10057, c_10058, c_80, c_10058, c_10058, c_10058, c_13792])).
% 11.74/4.51  tff(c_5248, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5239, c_5239, c_208])).
% 11.74/4.51  tff(c_10056, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10049, c_10049, c_10049, c_5248])).
% 11.74/4.51  tff(c_13835, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13810, c_10056])).
% 11.74/4.51  tff(c_11034, plain, (![C_1021, B_1022, A_1023]: (v1_funct_2(k2_funct_1(C_1021), B_1022, A_1023) | k2_relset_1(A_1023, B_1022, C_1021)!=B_1022 | ~v2_funct_1(C_1021) | ~m1_subset_1(C_1021, k1_zfmisc_1(k2_zfmisc_1(A_1023, B_1022))) | ~v1_funct_2(C_1021, A_1023, B_1022) | ~v1_funct_1(C_1021))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.74/4.51  tff(c_11052, plain, (![A_6, B_1022, A_1023]: (v1_funct_2(k2_funct_1(A_6), B_1022, A_1023) | k2_relset_1(A_1023, B_1022, A_6)!=B_1022 | ~v2_funct_1(A_6) | ~v1_funct_2(A_6, A_1023, B_1022) | ~v1_funct_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_1023, B_1022)))), inference(resolution, [status(thm)], [c_20, c_11034])).
% 11.74/4.51  tff(c_11383, plain, (![C_1051, B_1052, A_1053]: (m1_subset_1(k2_funct_1(C_1051), k1_zfmisc_1(k2_zfmisc_1(B_1052, A_1053))) | k2_relset_1(A_1053, B_1052, C_1051)!=B_1052 | ~v2_funct_1(C_1051) | ~m1_subset_1(C_1051, k1_zfmisc_1(k2_zfmisc_1(A_1053, B_1052))) | ~v1_funct_2(C_1051, A_1053, B_1052) | ~v1_funct_1(C_1051))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.74/4.51  tff(c_12955, plain, (![A_1174, B_1175, C_1176]: (k1_xboole_0=A_1174 | k1_relset_1(B_1175, A_1174, k2_funct_1(C_1176))=B_1175 | ~v1_funct_2(k2_funct_1(C_1176), B_1175, A_1174) | k2_relset_1(A_1174, B_1175, C_1176)!=B_1175 | ~v2_funct_1(C_1176) | ~m1_subset_1(C_1176, k1_zfmisc_1(k2_zfmisc_1(A_1174, B_1175))) | ~v1_funct_2(C_1176, A_1174, B_1175) | ~v1_funct_1(C_1176))), inference(resolution, [status(thm)], [c_11383, c_60])).
% 11.74/4.51  tff(c_14392, plain, (![A_1287, B_1288, A_1289]: (k1_xboole_0=A_1287 | k1_relset_1(B_1288, A_1287, k2_funct_1(A_1289))=B_1288 | ~v1_funct_2(k2_funct_1(A_1289), B_1288, A_1287) | k2_relset_1(A_1287, B_1288, A_1289)!=B_1288 | ~v2_funct_1(A_1289) | ~v1_funct_2(A_1289, A_1287, B_1288) | ~v1_funct_1(A_1289) | ~r1_tarski(A_1289, k2_zfmisc_1(A_1287, B_1288)))), inference(resolution, [status(thm)], [c_20, c_12955])).
% 11.74/4.51  tff(c_14437, plain, (![A_1290, B_1291, A_1292]: (k1_xboole_0=A_1290 | k1_relset_1(B_1291, A_1290, k2_funct_1(A_1292))=B_1291 | k2_relset_1(A_1290, B_1291, A_1292)!=B_1291 | ~v2_funct_1(A_1292) | ~v1_funct_2(A_1292, A_1290, B_1291) | ~v1_funct_1(A_1292) | ~r1_tarski(A_1292, k2_zfmisc_1(A_1290, B_1291)))), inference(resolution, [status(thm)], [c_11052, c_14392])).
% 11.74/4.51  tff(c_14457, plain, (![A_1290, B_1291]: (k1_xboole_0=A_1290 | k1_relset_1(B_1291, A_1290, k2_funct_1(k2_zfmisc_1(A_1290, B_1291)))=B_1291 | k2_relset_1(A_1290, B_1291, k2_zfmisc_1(A_1290, B_1291))!=B_1291 | ~v2_funct_1(k2_zfmisc_1(A_1290, B_1291)) | ~v1_funct_2(k2_zfmisc_1(A_1290, B_1291), A_1290, B_1291) | ~v1_funct_1(k2_zfmisc_1(A_1290, B_1291)))), inference(resolution, [status(thm)], [c_8, c_14437])).
% 11.74/4.51  tff(c_14466, plain, (![A_1293, B_1294]: (k1_xboole_0=A_1293 | k1_relset_1(B_1294, A_1293, k2_funct_1(k2_zfmisc_1(A_1293, B_1294)))=B_1294 | k2_relat_1(k2_zfmisc_1(A_1293, B_1294))!=B_1294 | ~v2_funct_1(k2_zfmisc_1(A_1293, B_1294)) | ~v1_funct_2(k2_zfmisc_1(A_1293, B_1294), A_1293, B_1294) | ~v1_funct_1(k2_zfmisc_1(A_1293, B_1294)))), inference(demodulation, [status(thm), theory('equality')], [c_10207, c_14457])).
% 11.74/4.51  tff(c_14518, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | k2_relat_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_funct_2(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10058, c_14466])).
% 11.74/4.51  tff(c_14551, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10058, c_10057, c_10058, c_80, c_10058, c_10058, c_14518])).
% 11.74/4.51  tff(c_14552, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_13835, c_14551])).
% 11.74/4.51  tff(c_4288, plain, (![C_485]: (v4_relat_1(C_485, k2_struct_0('#skF_1')) | ~m1_subset_1(C_485, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4176, c_4268])).
% 11.74/4.51  tff(c_30, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.74/4.51  tff(c_4360, plain, (![C_494]: (k7_relat_1(C_494, k2_struct_0('#skF_1'))=C_494 | ~v1_relat_1(C_494) | ~m1_subset_1(C_494, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_4288, c_30])).
% 11.74/4.51  tff(c_4363, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4188, c_4360])).
% 11.74/4.51  tff(c_4374, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_4363])).
% 11.74/4.51  tff(c_5244, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5239, c_4374])).
% 11.74/4.51  tff(c_14617, plain, (k7_relat_1('#skF_3', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14552, c_5244])).
% 11.74/4.51  tff(c_14612, plain, (k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14552, c_10058])).
% 11.74/4.51  tff(c_26, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.74/4.51  tff(c_4426, plain, (![A_500, B_501]: (k7_relat_1(k2_zfmisc_1(A_500, B_501), A_500)=k2_zfmisc_1(A_500, B_501) | ~v1_relat_1(k2_zfmisc_1(A_500, B_501)))), inference(resolution, [status(thm)], [c_4423, c_30])).
% 11.74/4.51  tff(c_4438, plain, (![A_500, B_501]: (k7_relat_1(k2_zfmisc_1(A_500, B_501), A_500)=k2_zfmisc_1(A_500, B_501))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4426])).
% 11.74/4.51  tff(c_14966, plain, (k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3'))=k7_relat_1('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14612, c_4438])).
% 11.74/4.51  tff(c_15049, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14617, c_14, c_14966])).
% 11.74/4.51  tff(c_15051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4267, c_15049])).
% 11.74/4.51  tff(c_15053, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4204])).
% 11.74/4.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.74/4.51  tff(c_15069, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15053, c_2])).
% 11.74/4.51  tff(c_15052, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4204])).
% 11.74/4.51  tff(c_15269, plain, (k2_struct_0('#skF_1')='#skF_3' | k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15053, c_15053, c_15052])).
% 11.74/4.51  tff(c_15270, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitLeft, [status(thm)], [c_15269])).
% 11.74/4.51  tff(c_15282, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15270, c_74])).
% 11.74/4.51  tff(c_15286, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_15069, c_15282])).
% 11.74/4.51  tff(c_15288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_15286])).
% 11.74/4.51  tff(c_15290, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(splitRight, [status(thm)], [c_15269])).
% 11.74/4.51  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.74/4.51  tff(c_15068, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15053, c_15053, c_32])).
% 11.74/4.51  tff(c_15066, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_15053, c_16])).
% 11.74/4.51  tff(c_15400, plain, (![A_1332, B_1333, C_1334]: (k2_relset_1(A_1332, B_1333, C_1334)=k2_relat_1(C_1334) | ~m1_subset_1(C_1334, k1_zfmisc_1(k2_zfmisc_1(A_1332, B_1333))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.74/4.51  tff(c_15404, plain, (![A_1332, B_1333]: (k2_relset_1(A_1332, B_1333, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15066, c_15400])).
% 11.74/4.51  tff(c_15416, plain, (![A_1332, B_1333]: (k2_relset_1(A_1332, B_1333, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15068, c_15404])).
% 11.74/4.51  tff(c_15289, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_15269])).
% 11.74/4.51  tff(c_15294, plain, (k2_relset_1('#skF_3', k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15289, c_202])).
% 11.74/4.51  tff(c_15418, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15416, c_15294])).
% 11.74/4.51  tff(c_15420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15290, c_15418])).
% 11.74/4.51  tff(c_15421, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_207])).
% 11.74/4.51  tff(c_16251, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16243, c_16243, c_16243, c_15421])).
% 11.74/4.51  tff(c_16612, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16392, c_16392, c_16251])).
% 11.74/4.51  tff(c_17511, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17506, c_16612])).
% 11.74/4.51  tff(c_17003, plain, (![C_1514, A_1515, B_1516]: (v1_funct_1(k2_funct_1(C_1514)) | k2_relset_1(A_1515, B_1516, C_1514)!=B_1516 | ~v2_funct_1(C_1514) | ~m1_subset_1(C_1514, k1_zfmisc_1(k2_zfmisc_1(A_1515, B_1516))) | ~v1_funct_2(C_1514, A_1515, B_1516) | ~v1_funct_1(C_1514))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.74/4.51  tff(c_17006, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16398, c_17003])).
% 11.74/4.51  tff(c_17023, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16401, c_80, c_16397, c_17006])).
% 11.74/4.51  tff(c_15577, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_15566, c_30])).
% 11.74/4.51  tff(c_15580, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15440, c_15577])).
% 11.74/4.51  tff(c_16248, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16243, c_15580])).
% 11.74/4.51  tff(c_28, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.74/4.51  tff(c_16293, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16248, c_28])).
% 11.74/4.51  tff(c_16297, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15440, c_16293])).
% 11.74/4.51  tff(c_16854, plain, (![A_1503, B_1504]: (k9_relat_1(k2_funct_1(A_1503), k9_relat_1(A_1503, B_1504))=B_1504 | ~r1_tarski(B_1504, k1_relat_1(A_1503)) | ~v2_funct_1(A_1503) | ~v1_funct_1(A_1503) | ~v1_relat_1(A_1503))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.74/4.51  tff(c_16869, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16297, c_16854])).
% 11.74/4.51  tff(c_16879, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15440, c_88, c_80, c_8, c_16869])).
% 11.74/4.51  tff(c_36, plain, (![A_20, B_22]: (k9_relat_1(k2_funct_1(A_20), k9_relat_1(A_20, B_22))=B_22 | ~r1_tarski(B_22, k1_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.74/4.51  tff(c_16887, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16879, c_36])).
% 11.74/4.51  tff(c_17048, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17023, c_16887])).
% 11.74/4.51  tff(c_17049, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_17048])).
% 11.74/4.51  tff(c_17228, plain, (![C_1541, B_1542, A_1543]: (m1_subset_1(k2_funct_1(C_1541), k1_zfmisc_1(k2_zfmisc_1(B_1542, A_1543))) | k2_relset_1(A_1543, B_1542, C_1541)!=B_1542 | ~v2_funct_1(C_1541) | ~m1_subset_1(C_1541, k1_zfmisc_1(k2_zfmisc_1(A_1543, B_1542))) | ~v1_funct_2(C_1541, A_1543, B_1542) | ~v1_funct_1(C_1541))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.74/4.51  tff(c_24, plain, (![B_13, A_11]: (v1_relat_1(B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.74/4.51  tff(c_17260, plain, (![C_1541, B_1542, A_1543]: (v1_relat_1(k2_funct_1(C_1541)) | ~v1_relat_1(k2_zfmisc_1(B_1542, A_1543)) | k2_relset_1(A_1543, B_1542, C_1541)!=B_1542 | ~v2_funct_1(C_1541) | ~m1_subset_1(C_1541, k1_zfmisc_1(k2_zfmisc_1(A_1543, B_1542))) | ~v1_funct_2(C_1541, A_1543, B_1542) | ~v1_funct_1(C_1541))), inference(resolution, [status(thm)], [c_17228, c_24])).
% 11.74/4.51  tff(c_17349, plain, (![C_1548, A_1549, B_1550]: (v1_relat_1(k2_funct_1(C_1548)) | k2_relset_1(A_1549, B_1550, C_1548)!=B_1550 | ~v2_funct_1(C_1548) | ~m1_subset_1(C_1548, k1_zfmisc_1(k2_zfmisc_1(A_1549, B_1550))) | ~v1_funct_2(C_1548, A_1549, B_1550) | ~v1_funct_1(C_1548))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_17260])).
% 11.74/4.51  tff(c_17355, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16398, c_17349])).
% 11.74/4.51  tff(c_17373, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16401, c_80, c_16397, c_17355])).
% 11.74/4.51  tff(c_17375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17049, c_17373])).
% 11.74/4.51  tff(c_17377, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_17048])).
% 11.74/4.51  tff(c_17532, plain, (![C_1570, B_1571, A_1572]: (m1_subset_1(k2_funct_1(C_1570), k1_zfmisc_1(k2_zfmisc_1(B_1571, A_1572))) | k2_relset_1(A_1572, B_1571, C_1570)!=B_1571 | ~v2_funct_1(C_1570) | ~m1_subset_1(C_1570, k1_zfmisc_1(k2_zfmisc_1(A_1572, B_1571))) | ~v1_funct_2(C_1570, A_1572, B_1571) | ~v1_funct_1(C_1570))), inference(cnfTransformation, [status(thm)], [f_153])).
% 11.74/4.51  tff(c_42, plain, (![C_28, A_26, B_27]: (v4_relat_1(C_28, A_26) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.74/4.51  tff(c_17985, plain, (![C_1611, B_1612, A_1613]: (v4_relat_1(k2_funct_1(C_1611), B_1612) | k2_relset_1(A_1613, B_1612, C_1611)!=B_1612 | ~v2_funct_1(C_1611) | ~m1_subset_1(C_1611, k1_zfmisc_1(k2_zfmisc_1(A_1613, B_1612))) | ~v1_funct_2(C_1611, A_1613, B_1612) | ~v1_funct_1(C_1611))), inference(resolution, [status(thm)], [c_17532, c_42])).
% 11.74/4.51  tff(c_17991, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16398, c_17985])).
% 11.74/4.51  tff(c_18009, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16401, c_80, c_16397, c_17991])).
% 11.74/4.51  tff(c_18018, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18009, c_30])).
% 11.74/4.51  tff(c_18024, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17377, c_18018])).
% 11.74/4.51  tff(c_18028, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18024, c_28])).
% 11.74/4.51  tff(c_18032, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17377, c_16879, c_18028])).
% 11.74/4.51  tff(c_18666, plain, (![B_1663, A_1664, C_1665]: (k2_relset_1(B_1663, A_1664, k2_funct_1(C_1665))=k2_relat_1(k2_funct_1(C_1665)) | k2_relset_1(A_1664, B_1663, C_1665)!=B_1663 | ~v2_funct_1(C_1665) | ~m1_subset_1(C_1665, k1_zfmisc_1(k2_zfmisc_1(A_1664, B_1663))) | ~v1_funct_2(C_1665, A_1664, B_1663) | ~v1_funct_1(C_1665))), inference(resolution, [status(thm)], [c_17532, c_44])).
% 11.74/4.51  tff(c_18672, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16398, c_18666])).
% 11.74/4.51  tff(c_18690, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16401, c_80, c_16397, c_18032, c_18672])).
% 11.74/4.51  tff(c_18692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17511, c_18690])).
% 11.74/4.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.74/4.51  
% 11.74/4.51  Inference rules
% 11.74/4.51  ----------------------
% 11.74/4.51  #Ref     : 0
% 11.74/4.51  #Sup     : 3792
% 11.74/4.51  #Fact    : 0
% 11.74/4.51  #Define  : 0
% 11.74/4.51  #Split   : 41
% 11.74/4.51  #Chain   : 0
% 11.74/4.51  #Close   : 0
% 11.74/4.51  
% 11.74/4.51  Ordering : KBO
% 11.74/4.51  
% 11.74/4.51  Simplification rules
% 11.74/4.51  ----------------------
% 11.74/4.51  #Subsume      : 1091
% 11.74/4.51  #Demod        : 5845
% 11.74/4.51  #Tautology    : 1216
% 11.74/4.51  #SimpNegUnit  : 161
% 11.74/4.51  #BackRed      : 331
% 11.74/4.51  
% 11.74/4.51  #Partial instantiations: 0
% 11.74/4.51  #Strategies tried      : 1
% 11.74/4.51  
% 11.74/4.51  Timing (in seconds)
% 11.74/4.51  ----------------------
% 11.74/4.52  Preprocessing        : 0.38
% 11.74/4.52  Parsing              : 0.21
% 11.74/4.52  CNF conversion       : 0.03
% 11.74/4.52  Main loop            : 3.22
% 11.74/4.52  Inferencing          : 0.97
% 11.74/4.52  Reduction            : 1.22
% 11.74/4.52  Demodulation         : 0.92
% 11.74/4.52  BG Simplification    : 0.09
% 11.74/4.52  Subsumption          : 0.71
% 11.74/4.52  Abstraction          : 0.14
% 11.74/4.52  MUC search           : 0.00
% 11.74/4.52  Cooper               : 0.00
% 11.74/4.52  Total                : 3.70
% 11.74/4.52  Index Insertion      : 0.00
% 11.74/4.52  Index Deletion       : 0.00
% 11.74/4.52  Index Matching       : 0.00
% 11.74/4.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
