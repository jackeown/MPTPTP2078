%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:19 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  176 (64040 expanded)
%              Number of leaves         :   44 (22555 expanded)
%              Depth                    :   28
%              Number of atoms          :  308 (200799 expanded)
%              Number of equality atoms :  131 (75482 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_167,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_28,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_143,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_85,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_93,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_85])).

tff(c_92,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_85])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_127,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_64])).

tff(c_148,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_148])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_16,plain,(
    ! [A_5] :
      ( k2_relat_1(k2_funct_1(A_5)) = k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1323,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1338,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_1323])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_133,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_62])).

tff(c_1353,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_133])).

tff(c_14,plain,(
    ! [A_4] : ~ v1_xboole_0(k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] : k3_tarski(k1_zfmisc_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_179,plain,(
    ! [A_56] :
      ( m1_subset_1('#skF_1'(A_56),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_188,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_179])).

tff(c_193,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_188])).

tff(c_194,plain,(
    m1_subset_1('#skF_1'('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_193])).

tff(c_158,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [A_21,B_24] :
      ( k3_tarski(A_21) != k1_xboole_0
      | ~ r2_hidden(B_24,A_21)
      | k1_xboole_0 = B_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1236,plain,(
    ! [A_118,B_119] :
      ( k3_tarski(A_118) != k1_xboole_0
      | k1_xboole_0 = B_119
      | ~ m1_subset_1(B_119,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_158,c_44])).

tff(c_1239,plain,
    ( k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4'))) != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_194,c_1236])).

tff(c_1253,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1239])).

tff(c_1254,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1253])).

tff(c_1263,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1254])).

tff(c_1362,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1263])).

tff(c_66,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_94,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_66])).

tff(c_118,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_94])).

tff(c_1366,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_118])).

tff(c_1302,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1317,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_1302])).

tff(c_1359,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1317])).

tff(c_1365,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_127])).

tff(c_1475,plain,(
    ! [B_141,A_142,C_143] :
      ( k1_xboole_0 = B_141
      | k1_relset_1(A_142,B_141,C_143) = A_142
      | ~ v1_funct_2(C_143,A_142,B_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1478,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1365,c_1475])).

tff(c_1489,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1359,c_1478])).

tff(c_1490,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1362,c_1489])).

tff(c_1521,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1366])).

tff(c_1358,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1338])).

tff(c_1517,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1358])).

tff(c_1518,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1365])).

tff(c_1705,plain,(
    ! [A_161,B_162,C_163] :
      ( k2_tops_2(A_161,B_162,C_163) = k2_funct_1(C_163)
      | ~ v2_funct_1(C_163)
      | k2_relset_1(A_161,B_162,C_163) != B_162
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_2(C_163,A_161,B_162)
      | ~ v1_funct_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1711,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1518,c_1705])).

tff(c_1723,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1521,c_1517,c_60,c_1711])).

tff(c_1628,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1(k2_tops_2(A_154,B_155,C_156),k1_zfmisc_1(k2_zfmisc_1(B_155,A_154)))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_2(C_156,A_154,B_155)
      | ~ v1_funct_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_24,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1746,plain,(
    ! [B_164,A_165,C_166] :
      ( k2_relset_1(B_164,A_165,k2_tops_2(A_165,B_164,C_166)) = k2_relat_1(k2_tops_2(A_165,B_164,C_166))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164)))
      | ~ v1_funct_2(C_166,A_165,B_164)
      | ~ v1_funct_1(C_166) ) ),
    inference(resolution,[status(thm)],[c_1628,c_24])).

tff(c_1750,plain,
    ( k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) = k2_relat_1(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1518,c_1746])).

tff(c_1760,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1521,c_1723,c_1723,c_1750])).

tff(c_264,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_279,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_264])).

tff(c_298,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_133])).

tff(c_202,plain,(
    ! [A_57,B_58] :
      ( k3_tarski(A_57) != k1_xboole_0
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_158,c_44])).

tff(c_205,plain,
    ( k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4'))) != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_194,c_202])).

tff(c_219,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_205])).

tff(c_220,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_219])).

tff(c_229,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_306,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_229])).

tff(c_309,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_118])).

tff(c_281,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_296,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_281])).

tff(c_353,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_296])).

tff(c_308,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_127])).

tff(c_428,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_431,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_308,c_428])).

tff(c_442,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_353,c_431])).

tff(c_443,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_442])).

tff(c_453,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_309])).

tff(c_303,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_279])).

tff(c_451,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_303])).

tff(c_449,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_308])).

tff(c_675,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_tops_2(A_104,B_105,C_106) = k2_funct_1(C_106)
      | ~ v2_funct_1(C_106)
      | k2_relset_1(A_104,B_105,C_106) != B_105
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(C_106,A_104,B_105)
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_681,plain,
    ( k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_449,c_675])).

tff(c_693,plain,(
    k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_453,c_451,c_60,c_681])).

tff(c_58,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_195,plain,
    ( k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3')
    | k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_92,c_92,c_93,c_93,c_92,c_92,c_58])).

tff(c_196,plain,(
    k1_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_304,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_298,c_298,c_196])).

tff(c_448,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_443,c_304])).

tff(c_700,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_448])).

tff(c_534,plain,(
    ! [A_86,B_87,C_88] :
      ( v1_funct_2(k2_tops_2(A_86,B_87,C_88),B_87,A_86)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_2(C_88,A_86,B_87)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_536,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_449,c_534])).

tff(c_545,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_453,c_536])).

tff(c_699,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_545])).

tff(c_52,plain,(
    ! [A_28,B_29,C_30] :
      ( m1_subset_1(k2_tops_2(A_28,B_29,C_30),k1_zfmisc_1(k2_zfmisc_1(B_29,A_28)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_705,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_52])).

tff(c_709,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_453,c_449,c_705])).

tff(c_36,plain,(
    ! [B_16,A_15,C_17] :
      ( k1_xboole_0 = B_16
      | k1_relset_1(A_15,B_16,C_17) = A_15
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_727,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_709,c_36])).

tff(c_763,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_727])).

tff(c_764,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_700,c_763])).

tff(c_776,plain,(
    v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_699])).

tff(c_775,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_709])).

tff(c_28,plain,(
    ! [C_17,A_15] :
      ( k1_xboole_0 = C_17
      | ~ v1_funct_2(C_17,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_972,plain,
    ( k2_funct_1('#skF_5') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_5'),k2_relat_1('#skF_5'),k1_xboole_0)
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_775,c_28])).

tff(c_1018,plain,
    ( k2_funct_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_972])).

tff(c_1019,plain,(
    k2_funct_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_1018])).

tff(c_18,plain,(
    ! [A_5] :
      ( k1_relat_1(k2_funct_1(A_5)) = k2_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1042,plain,
    ( k2_relat_1('#skF_5') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_18])).

tff(c_1048,plain,(
    k2_relat_1('#skF_5') = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_68,c_60,c_1042])).

tff(c_777,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_xboole_0,k2_funct_1('#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_700])).

tff(c_1029,plain,(
    k1_relset_1(k2_relat_1('#skF_5'),k1_xboole_0,k1_xboole_0) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_777])).

tff(c_1117,plain,(
    k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1048,c_1029])).

tff(c_1028,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1019,c_775])).

tff(c_1118,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1028])).

tff(c_22,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1148,plain,(
    k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1118,c_22])).

tff(c_1200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1117,c_1148])).

tff(c_1201,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_40,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_1'(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1219,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1201,c_40])).

tff(c_1226,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2,c_1219])).

tff(c_1228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1226])).

tff(c_1229,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_1363,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_relat_1('#skF_5'),'#skF_5')) != k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1353,c_1229])).

tff(c_1515,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_tops_2(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1490,c_1490,c_1490,c_1363])).

tff(c_1730,plain,(
    k2_relset_1(k2_relat_1('#skF_5'),k1_relat_1('#skF_5'),k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_1515])).

tff(c_1845,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1760,c_1730])).

tff(c_1852,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1845])).

tff(c_1856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_68,c_60,c_1852])).

tff(c_1857,plain,(
    '#skF_1'('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1254])).

tff(c_1866,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1857,c_40])).

tff(c_1873,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2,c_1866])).

tff(c_1875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.78  
% 4.34/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.35/1.78  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.35/1.78  
% 4.35/1.78  %Foreground sorts:
% 4.35/1.78  
% 4.35/1.78  
% 4.35/1.78  %Background operators:
% 4.35/1.78  
% 4.35/1.78  
% 4.35/1.78  %Foreground operators:
% 4.35/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.35/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.35/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.35/1.78  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.35/1.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.35/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.35/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.35/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.35/1.78  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.35/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.35/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.35/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.35/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.35/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.35/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.35/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.35/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.35/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.35/1.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.35/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.35/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.35/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.78  
% 4.44/1.81  tff(f_167, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 4.44/1.81  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.44/1.81  tff(f_88, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.44/1.81  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.44/1.81  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.44/1.81  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.44/1.81  tff(f_44, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.44/1.81  tff(f_28, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.44/1.81  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_struct_0)).
% 4.44/1.81  tff(f_41, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.44/1.81  tff(f_119, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 4.44/1.81  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.44/1.81  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.44/1.81  tff(f_131, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.44/1.81  tff(f_143, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 4.44/1.81  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_70, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.44/1.81  tff(c_74, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_85, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.44/1.81  tff(c_93, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_85])).
% 4.44/1.81  tff(c_92, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_70, c_85])).
% 4.44/1.81  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_127, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_92, c_64])).
% 4.44/1.81  tff(c_148, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.44/1.81  tff(c_156, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_127, c_148])).
% 4.44/1.81  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_16, plain, (![A_5]: (k2_relat_1(k2_funct_1(A_5))=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.44/1.81  tff(c_1323, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.44/1.81  tff(c_1338, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_127, c_1323])).
% 4.44/1.81  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_133, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_92, c_62])).
% 4.44/1.81  tff(c_1353, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_133])).
% 4.44/1.81  tff(c_14, plain, (![A_4]: (~v1_xboole_0(k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.44/1.81  tff(c_4, plain, (![A_1]: (k3_tarski(k1_zfmisc_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.44/1.81  tff(c_179, plain, (![A_56]: (m1_subset_1('#skF_1'(A_56), k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.44/1.81  tff(c_188, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_92, c_179])).
% 4.44/1.81  tff(c_193, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_188])).
% 4.44/1.81  tff(c_194, plain, (m1_subset_1('#skF_1'('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_193])).
% 4.44/1.81  tff(c_158, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.44/1.81  tff(c_44, plain, (![A_21, B_24]: (k3_tarski(A_21)!=k1_xboole_0 | ~r2_hidden(B_24, A_21) | k1_xboole_0=B_24)), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.44/1.81  tff(c_1236, plain, (![A_118, B_119]: (k3_tarski(A_118)!=k1_xboole_0 | k1_xboole_0=B_119 | ~m1_subset_1(B_119, A_118) | v1_xboole_0(A_118))), inference(resolution, [status(thm)], [c_158, c_44])).
% 4.44/1.81  tff(c_1239, plain, (k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4')))!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_194, c_1236])).
% 4.44/1.81  tff(c_1253, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1239])).
% 4.44/1.81  tff(c_1254, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14, c_1253])).
% 4.44/1.81  tff(c_1263, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1254])).
% 4.44/1.81  tff(c_1362, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1263])).
% 4.44/1.81  tff(c_66, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.44/1.81  tff(c_94, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_66])).
% 4.44/1.81  tff(c_118, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_94])).
% 4.44/1.81  tff(c_1366, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_118])).
% 4.44/1.81  tff(c_1302, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.44/1.81  tff(c_1317, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_127, c_1302])).
% 4.44/1.81  tff(c_1359, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1317])).
% 4.44/1.81  tff(c_1365, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_127])).
% 4.44/1.81  tff(c_1475, plain, (![B_141, A_142, C_143]: (k1_xboole_0=B_141 | k1_relset_1(A_142, B_141, C_143)=A_142 | ~v1_funct_2(C_143, A_142, B_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.44/1.81  tff(c_1478, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_struct_0('#skF_3') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1365, c_1475])).
% 4.44/1.81  tff(c_1489, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1359, c_1478])).
% 4.44/1.81  tff(c_1490, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1362, c_1489])).
% 4.44/1.81  tff(c_1521, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1366])).
% 4.44/1.81  tff(c_1358, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1338])).
% 4.44/1.81  tff(c_1517, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1358])).
% 4.44/1.81  tff(c_1518, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1365])).
% 4.44/1.81  tff(c_1705, plain, (![A_161, B_162, C_163]: (k2_tops_2(A_161, B_162, C_163)=k2_funct_1(C_163) | ~v2_funct_1(C_163) | k2_relset_1(A_161, B_162, C_163)!=B_162 | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_2(C_163, A_161, B_162) | ~v1_funct_1(C_163))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.44/1.81  tff(c_1711, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1518, c_1705])).
% 4.44/1.81  tff(c_1723, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1521, c_1517, c_60, c_1711])).
% 4.44/1.81  tff(c_1628, plain, (![A_154, B_155, C_156]: (m1_subset_1(k2_tops_2(A_154, B_155, C_156), k1_zfmisc_1(k2_zfmisc_1(B_155, A_154))) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_2(C_156, A_154, B_155) | ~v1_funct_1(C_156))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.44/1.81  tff(c_24, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.44/1.81  tff(c_1746, plain, (![B_164, A_165, C_166]: (k2_relset_1(B_164, A_165, k2_tops_2(A_165, B_164, C_166))=k2_relat_1(k2_tops_2(A_165, B_164, C_166)) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))) | ~v1_funct_2(C_166, A_165, B_164) | ~v1_funct_1(C_166))), inference(resolution, [status(thm)], [c_1628, c_24])).
% 4.44/1.81  tff(c_1750, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))=k2_relat_1(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1518, c_1746])).
% 4.44/1.81  tff(c_1760, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1521, c_1723, c_1723, c_1750])).
% 4.44/1.81  tff(c_264, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.44/1.81  tff(c_279, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_127, c_264])).
% 4.44/1.81  tff(c_298, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_133])).
% 4.44/1.81  tff(c_202, plain, (![A_57, B_58]: (k3_tarski(A_57)!=k1_xboole_0 | k1_xboole_0=B_58 | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_158, c_44])).
% 4.44/1.81  tff(c_205, plain, (k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_4')))!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_194, c_202])).
% 4.44/1.81  tff(c_219, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_205])).
% 4.44/1.81  tff(c_220, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | '#skF_1'('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_14, c_219])).
% 4.44/1.81  tff(c_229, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_220])).
% 4.44/1.81  tff(c_306, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_298, c_229])).
% 4.44/1.81  tff(c_309, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_118])).
% 4.44/1.81  tff(c_281, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.44/1.81  tff(c_296, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_127, c_281])).
% 4.44/1.81  tff(c_353, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_296])).
% 4.44/1.81  tff(c_308, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_127])).
% 4.52/1.81  tff(c_428, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.52/1.81  tff(c_431, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_struct_0('#skF_3') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_308, c_428])).
% 4.52/1.81  tff(c_442, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_353, c_431])).
% 4.52/1.81  tff(c_443, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_306, c_442])).
% 4.52/1.81  tff(c_453, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_309])).
% 4.52/1.81  tff(c_303, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_279])).
% 4.52/1.81  tff(c_451, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_303])).
% 4.52/1.81  tff(c_449, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_308])).
% 4.52/1.81  tff(c_675, plain, (![A_104, B_105, C_106]: (k2_tops_2(A_104, B_105, C_106)=k2_funct_1(C_106) | ~v2_funct_1(C_106) | k2_relset_1(A_104, B_105, C_106)!=B_105 | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(C_106, A_104, B_105) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.52/1.81  tff(c_681, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_449, c_675])).
% 4.52/1.81  tff(c_693, plain, (k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_453, c_451, c_60, c_681])).
% 4.52/1.81  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.52/1.81  tff(c_195, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3') | k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_92, c_92, c_93, c_93, c_92, c_92, c_58])).
% 4.52/1.81  tff(c_196, plain, (k1_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_195])).
% 4.52/1.81  tff(c_304, plain, (k1_relset_1(k2_relat_1('#skF_5'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_298, c_298, c_196])).
% 4.52/1.81  tff(c_448, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_443, c_304])).
% 4.52/1.81  tff(c_700, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_448])).
% 4.52/1.81  tff(c_534, plain, (![A_86, B_87, C_88]: (v1_funct_2(k2_tops_2(A_86, B_87, C_88), B_87, A_86) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_2(C_88, A_86, B_87) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.52/1.81  tff(c_536, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_449, c_534])).
% 4.52/1.81  tff(c_545, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_453, c_536])).
% 4.52/1.81  tff(c_699, plain, (v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_545])).
% 4.52/1.81  tff(c_52, plain, (![A_28, B_29, C_30]: (m1_subset_1(k2_tops_2(A_28, B_29, C_30), k1_zfmisc_1(k2_zfmisc_1(B_29, A_28))) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.52/1.81  tff(c_705, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_693, c_52])).
% 4.52/1.81  tff(c_709, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_453, c_449, c_705])).
% 4.52/1.81  tff(c_36, plain, (![B_16, A_15, C_17]: (k1_xboole_0=B_16 | k1_relset_1(A_15, B_16, C_17)=A_15 | ~v1_funct_2(C_17, A_15, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.52/1.81  tff(c_727, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1('#skF_5') | ~v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_709, c_36])).
% 4.52/1.81  tff(c_763, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_727])).
% 4.52/1.81  tff(c_764, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_700, c_763])).
% 4.52/1.81  tff(c_776, plain, (v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_764, c_699])).
% 4.52/1.81  tff(c_775, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_764, c_709])).
% 4.52/1.81  tff(c_28, plain, (![C_17, A_15]: (k1_xboole_0=C_17 | ~v1_funct_2(C_17, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.52/1.81  tff(c_972, plain, (k2_funct_1('#skF_5')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_5'), k2_relat_1('#skF_5'), k1_xboole_0) | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_775, c_28])).
% 4.52/1.81  tff(c_1018, plain, (k2_funct_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_776, c_972])).
% 4.52/1.81  tff(c_1019, plain, (k2_funct_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_306, c_1018])).
% 4.52/1.81  tff(c_18, plain, (![A_5]: (k1_relat_1(k2_funct_1(A_5))=k2_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.52/1.81  tff(c_1042, plain, (k2_relat_1('#skF_5')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_18])).
% 4.52/1.81  tff(c_1048, plain, (k2_relat_1('#skF_5')=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_68, c_60, c_1042])).
% 4.52/1.81  tff(c_777, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_xboole_0, k2_funct_1('#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_764, c_700])).
% 4.52/1.81  tff(c_1029, plain, (k1_relset_1(k2_relat_1('#skF_5'), k1_xboole_0, k1_xboole_0)!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_777])).
% 4.52/1.81  tff(c_1117, plain, (k1_relset_1(k1_relat_1(k1_xboole_0), k1_xboole_0, k1_xboole_0)!=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_1048, c_1029])).
% 4.52/1.81  tff(c_1028, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1019, c_775])).
% 4.52/1.81  tff(c_1118, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_1028])).
% 4.52/1.81  tff(c_22, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.52/1.81  tff(c_1148, plain, (k1_relset_1(k1_relat_1(k1_xboole_0), k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1118, c_22])).
% 4.52/1.81  tff(c_1200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1117, c_1148])).
% 4.52/1.81  tff(c_1201, plain, ('#skF_1'('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_220])).
% 4.52/1.81  tff(c_40, plain, (![A_19]: (~v1_xboole_0('#skF_1'(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.52/1.81  tff(c_1219, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1201, c_40])).
% 4.52/1.81  tff(c_1226, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2, c_1219])).
% 4.52/1.81  tff(c_1228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1226])).
% 4.52/1.81  tff(c_1229, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_195])).
% 4.52/1.81  tff(c_1363, plain, (k2_relset_1(k2_relat_1('#skF_5'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_relat_1('#skF_5'), '#skF_5'))!=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1353, c_1229])).
% 4.52/1.81  tff(c_1515, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_tops_2(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1490, c_1490, c_1490, c_1363])).
% 4.52/1.81  tff(c_1730, plain, (k2_relset_1(k2_relat_1('#skF_5'), k1_relat_1('#skF_5'), k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_1515])).
% 4.52/1.81  tff(c_1845, plain, (k2_relat_1(k2_funct_1('#skF_5'))!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1760, c_1730])).
% 4.52/1.81  tff(c_1852, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1845])).
% 4.52/1.81  tff(c_1856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_68, c_60, c_1852])).
% 4.52/1.81  tff(c_1857, plain, ('#skF_1'('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1254])).
% 4.52/1.81  tff(c_1866, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1857, c_40])).
% 4.52/1.81  tff(c_1873, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2, c_1866])).
% 4.52/1.81  tff(c_1875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1873])).
% 4.52/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.81  
% 4.52/1.81  Inference rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Ref     : 0
% 4.52/1.81  #Sup     : 370
% 4.52/1.81  #Fact    : 0
% 4.52/1.81  #Define  : 0
% 4.52/1.81  #Split   : 8
% 4.52/1.81  #Chain   : 0
% 4.52/1.81  #Close   : 0
% 4.52/1.81  
% 4.52/1.81  Ordering : KBO
% 4.52/1.81  
% 4.52/1.81  Simplification rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Subsume      : 69
% 4.52/1.81  #Demod        : 376
% 4.52/1.81  #Tautology    : 168
% 4.52/1.81  #SimpNegUnit  : 71
% 4.52/1.81  #BackRed      : 80
% 4.52/1.81  
% 4.52/1.81  #Partial instantiations: 0
% 4.52/1.81  #Strategies tried      : 1
% 4.52/1.81  
% 4.52/1.81  Timing (in seconds)
% 4.52/1.81  ----------------------
% 4.52/1.82  Preprocessing        : 0.40
% 4.52/1.82  Parsing              : 0.21
% 4.52/1.82  CNF conversion       : 0.02
% 4.52/1.82  Main loop            : 0.56
% 4.52/1.82  Inferencing          : 0.19
% 4.52/1.82  Reduction            : 0.20
% 4.52/1.82  Demodulation         : 0.13
% 4.52/1.82  BG Simplification    : 0.03
% 4.52/1.82  Subsumption          : 0.09
% 4.52/1.82  Abstraction          : 0.03
% 4.52/1.82  MUC search           : 0.00
% 4.52/1.82  Cooper               : 0.00
% 4.52/1.82  Total                : 1.03
% 4.52/1.82  Index Insertion      : 0.00
% 4.52/1.82  Index Deletion       : 0.00
% 4.52/1.82  Index Matching       : 0.00
% 4.52/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
