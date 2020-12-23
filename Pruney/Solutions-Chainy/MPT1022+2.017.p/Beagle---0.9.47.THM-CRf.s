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
% DateTime   : Thu Dec  3 10:16:15 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :  211 (2435 expanded)
%              Number of leaves         :   44 ( 863 expanded)
%              Depth                    :   25
%              Number of atoms          :  431 (6844 expanded)
%              Number of equality atoms :   86 (1204 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_149,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_58,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_70,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_70])).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_73])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_62,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1133,plain,(
    ! [C_180,A_181,B_182] :
      ( v2_funct_1(C_180)
      | ~ v3_funct_2(C_180,A_181,B_182)
      | ~ v1_funct_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1142,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1133])).

tff(c_1149,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1142])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_629,plain,(
    ! [C_122,B_123,A_124] :
      ( v5_relat_1(C_122,B_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_633,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_629])).

tff(c_646,plain,(
    ! [B_127,A_128] :
      ( k2_relat_1(B_127) = A_128
      | ~ v2_funct_2(B_127,A_128)
      | ~ v5_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_649,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_633,c_646])).

tff(c_652,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_649])).

tff(c_653,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_823,plain,(
    ! [C_156,B_157,A_158] :
      ( v2_funct_2(C_156,B_157)
      | ~ v3_funct_2(C_156,A_158,B_157)
      | ~ v1_funct_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_829,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_823])).

tff(c_833,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_829])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_653,c_833])).

tff(c_836,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_858,plain,(
    ! [A_159] :
      ( m1_subset_1(A_159,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_159),k2_relat_1(A_159))))
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_870,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_858])).

tff(c_880,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_870])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_892,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_880,c_24])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_898,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_892,c_14])).

tff(c_901,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_898])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_905,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_12])).

tff(c_909,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_836,c_905])).

tff(c_1237,plain,(
    ! [A_194,B_195] :
      ( k9_relat_1(k2_funct_1(A_194),k9_relat_1(A_194,B_195)) = B_195
      | ~ r1_tarski(B_195,k1_relat_1(A_194))
      | ~ v2_funct_1(A_194)
      | ~ v1_funct_1(A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1267,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_1237])).

tff(c_1282,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_1149,c_6,c_1267])).

tff(c_22,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_925,plain,(
    ! [A_164] :
      ( v5_relat_1(A_164,k2_relat_1(A_164))
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(resolution,[status(thm)],[c_858,c_22])).

tff(c_36,plain,(
    ! [B_34] :
      ( v2_funct_2(B_34,k2_relat_1(B_34))
      | ~ v5_relat_1(B_34,k2_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_964,plain,(
    ! [A_167] :
      ( v2_funct_2(A_167,k2_relat_1(A_167))
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_925,c_36])).

tff(c_1454,plain,(
    ! [B_204,A_205] :
      ( v2_funct_2(k7_relat_1(B_204,A_205),k9_relat_1(B_204,A_205))
      | ~ v1_funct_1(k7_relat_1(B_204,A_205))
      | ~ v1_relat_1(k7_relat_1(B_204,A_205))
      | ~ v1_relat_1(B_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_964])).

tff(c_1460,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_1454])).

tff(c_1543,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1460])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1544,plain,(
    ! [A_209,B_210] :
      ( k2_funct_2(A_209,B_210) = k2_funct_1(B_210)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209)))
      | ~ v3_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1547,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1544])).

tff(c_1550,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1547])).

tff(c_1738,plain,(
    ! [A_222,B_223] :
      ( m1_subset_1(k2_funct_2(A_222,B_223),k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ v3_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1770,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_1738])).

tff(c_1785,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_1770])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1814,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1785,c_8])).

tff(c_1839,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1814])).

tff(c_1841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1543,c_1839])).

tff(c_1843,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_3297,plain,(
    ! [A_278,B_279] :
      ( k2_funct_2(A_278,B_279) = k2_funct_1(B_279)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_zfmisc_1(A_278,A_278)))
      | ~ v3_funct_2(B_279,A_278,A_278)
      | ~ v1_funct_2(B_279,A_278,A_278)
      | ~ v1_funct_1(B_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3300,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3297])).

tff(c_3303,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_3300])).

tff(c_1535,plain,(
    ! [A_207,B_208] :
      ( v1_funct_1(k2_funct_2(A_207,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ v3_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1538,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1535])).

tff(c_1541,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1538])).

tff(c_3304,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3303,c_1541])).

tff(c_3466,plain,(
    ! [A_281,B_282] :
      ( v3_funct_2(k2_funct_2(A_281,B_282),A_281,A_281)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(k2_zfmisc_1(A_281,A_281)))
      | ~ v3_funct_2(B_282,A_281,A_281)
      | ~ v1_funct_2(B_282,A_281,A_281)
      | ~ v1_funct_1(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3468,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3466])).

tff(c_3471,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_3303,c_3468])).

tff(c_3858,plain,(
    ! [A_291,B_292] :
      ( m1_subset_1(k2_funct_2(A_291,B_292),k1_zfmisc_1(k2_zfmisc_1(A_291,A_291)))
      | ~ m1_subset_1(B_292,k1_zfmisc_1(k2_zfmisc_1(A_291,A_291)))
      | ~ v3_funct_2(B_292,A_291,A_291)
      | ~ v1_funct_2(B_292,A_291,A_291)
      | ~ v1_funct_1(B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3890,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3303,c_3858])).

tff(c_3905,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_3890])).

tff(c_30,plain,(
    ! [C_32,B_31,A_30] :
      ( v2_funct_2(C_32,B_31)
      | ~ v3_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3918,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3905,c_30])).

tff(c_3949,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3304,c_3471,c_3918])).

tff(c_3955,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3905,c_22])).

tff(c_38,plain,(
    ! [B_34,A_33] :
      ( k2_relat_1(B_34) = A_33
      | ~ v2_funct_2(B_34,A_33)
      | ~ v5_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3962,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3955,c_38])).

tff(c_3965,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_3949,c_3962])).

tff(c_3956,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3905,c_24])).

tff(c_3968,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3956,c_14])).

tff(c_3971,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_3968])).

tff(c_2630,plain,(
    ! [A_249,B_250] :
      ( k2_funct_2(A_249,B_250) = k2_funct_1(B_250)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(k2_zfmisc_1(A_249,A_249)))
      | ~ v3_funct_2(B_250,A_249,A_249)
      | ~ v1_funct_2(B_250,A_249,A_249)
      | ~ v1_funct_1(B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2633,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2630])).

tff(c_2636,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2633])).

tff(c_3113,plain,(
    ! [A_276,B_277] :
      ( m1_subset_1(k2_funct_2(A_276,B_277),k1_zfmisc_1(k2_zfmisc_1(A_276,A_276)))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_zfmisc_1(A_276,A_276)))
      | ~ v3_funct_2(B_277,A_276,A_276)
      | ~ v1_funct_2(B_277,A_276,A_276)
      | ~ v1_funct_1(B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3145,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2636,c_3113])).

tff(c_3160,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_3145])).

tff(c_3211,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3160,c_24])).

tff(c_3223,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3211,c_14])).

tff(c_3226,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_3223])).

tff(c_1865,plain,(
    ! [A_225,B_226] :
      ( k2_funct_2(A_225,B_226) = k2_funct_1(B_226)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ v3_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_1(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1868,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1865])).

tff(c_1871,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1868])).

tff(c_1872,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_1541])).

tff(c_2444,plain,(
    ! [A_247,B_248] :
      ( m1_subset_1(k2_funct_2(A_247,B_248),k1_zfmisc_1(k2_zfmisc_1(A_247,A_247)))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(k2_zfmisc_1(A_247,A_247)))
      | ~ v3_funct_2(B_248,A_247,A_247)
      | ~ v1_funct_2(B_248,A_247,A_247)
      | ~ v1_funct_1(B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2476,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_2444])).

tff(c_2491,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_2476])).

tff(c_2542,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2491,c_24])).

tff(c_2554,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2542,c_14])).

tff(c_2557,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_2554])).

tff(c_1842,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_1844,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1842])).

tff(c_2622,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_1844])).

tff(c_2626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_2622])).

tff(c_2627,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1842])).

tff(c_2629,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2627])).

tff(c_3290,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_2629])).

tff(c_3294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_3290])).

tff(c_3296,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2627])).

tff(c_3295,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2627])).

tff(c_2628,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1842])).

tff(c_1401,plain,(
    ! [B_202,A_203] :
      ( v5_relat_1(k7_relat_1(B_202,A_203),k9_relat_1(B_202,A_203))
      | ~ v1_funct_1(k7_relat_1(B_202,A_203))
      | ~ v1_relat_1(k7_relat_1(B_202,A_203))
      | ~ v1_relat_1(B_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_925])).

tff(c_1410,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_1401])).

tff(c_3310,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_3296,c_2628,c_1410])).

tff(c_3313,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_3310,c_38])).

tff(c_3316,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3296,c_3295,c_3313])).

tff(c_4044,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3971,c_3316])).

tff(c_4050,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_4044])).

tff(c_595,plain,(
    ! [C_115,A_116,B_117] :
      ( v4_relat_1(C_115,A_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_599,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_595])).

tff(c_609,plain,(
    ! [B_120,A_121] :
      ( k7_relat_1(B_120,A_121) = B_120
      | ~ v4_relat_1(B_120,A_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_612,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_599,c_609])).

tff(c_615,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_612])).

tff(c_619,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_12])).

tff(c_623,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_619])).

tff(c_838,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_623])).

tff(c_1270,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_1237])).

tff(c_1284,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_1149,c_1270])).

tff(c_1292,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_1284])).

tff(c_1293,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1292])).

tff(c_4075,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4050,c_1293])).

tff(c_4086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4075])).

tff(c_4087,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1292])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,k9_relat_1(B_15,A_14)) = A_14
      | ~ v2_funct_1(B_15)
      | ~ r1_tarski(A_14,k1_relat_1(B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4113,plain,(
    ! [A_14] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_14)) = A_14
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_14,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4087,c_18])).

tff(c_4169,plain,(
    ! [A_295] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_295)) = A_295
      | ~ r1_tarski(A_295,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_1149,c_4113])).

tff(c_1095,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k8_relset_1(A_175,B_176,C_177,D_178) = k10_relat_1(C_177,D_178)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1104,plain,(
    ! [D_178] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_178) = k10_relat_1('#skF_3',D_178) ),
    inference(resolution,[status(thm)],[c_60,c_1095])).

tff(c_911,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k7_relset_1(A_160,B_161,C_162,D_163) = k9_relat_1(C_162,D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_920,plain,(
    ! [D_163] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_163) = k9_relat_1('#skF_3',D_163) ),
    inference(resolution,[status(thm)],[c_60,c_911])).

tff(c_98,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_102,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_98])).

tff(c_136,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(B_59) = A_60
      | ~ v2_funct_2(B_59,A_60)
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_139,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_136])).

tff(c_142,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_139])).

tff(c_161,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_285,plain,(
    ! [C_86,B_87,A_88] :
      ( v2_funct_2(C_86,B_87)
      | ~ v3_funct_2(C_86,A_88,B_87)
      | ~ v1_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_291,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_285])).

tff(c_295,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_291])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_295])).

tff(c_298,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_359,plain,(
    ! [B_89,A_90] :
      ( k9_relat_1(B_89,k10_relat_1(B_89,A_90)) = A_90
      | ~ r1_tarski(A_90,k2_relat_1(B_89))
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_361,plain,(
    ! [A_90] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_90)) = A_90
      | ~ r1_tarski(A_90,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_359])).

tff(c_368,plain,(
    ! [A_90] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_90)) = A_90
      | ~ r1_tarski(A_90,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_66,c_361])).

tff(c_555,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k8_relset_1(A_108,B_109,C_110,D_111) = k10_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_564,plain,(
    ! [D_111] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_111) = k10_relat_1('#skF_3',D_111) ),
    inference(resolution,[status(thm)],[c_60,c_555])).

tff(c_516,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k7_relset_1(A_101,B_102,C_103,D_104) = k9_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_525,plain,(
    ! [D_104] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_104) = k9_relat_1('#skF_3',D_104) ),
    inference(resolution,[status(thm)],[c_60,c_516])).

tff(c_56,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_77,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_527,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_77])).

tff(c_565,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_527])).

tff(c_577,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_565])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_577])).

tff(c_582,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_948,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_582])).

tff(c_1106,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_948])).

tff(c_4175,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4169,c_1106])).

tff(c_4206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.02  
% 5.36/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.02  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.36/2.02  
% 5.36/2.02  %Foreground sorts:
% 5.36/2.02  
% 5.36/2.02  
% 5.36/2.02  %Background operators:
% 5.36/2.02  
% 5.36/2.02  
% 5.36/2.02  %Foreground operators:
% 5.36/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.36/2.02  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.36/2.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.36/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.36/2.02  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.36/2.02  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.36/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.36/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.36/2.02  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.36/2.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.36/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.36/2.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.36/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.36/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.36/2.02  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.36/2.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.36/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.36/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.36/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.36/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.36/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.36/2.02  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.36/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.36/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.36/2.02  
% 5.36/2.05  tff(f_164, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 5.36/2.05  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.36/2.05  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.36/2.05  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.36/2.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.36/2.05  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.36/2.05  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.36/2.05  tff(f_149, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.36/2.05  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.36/2.05  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.36/2.05  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 5.36/2.05  tff(f_139, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.36/2.05  tff(f_129, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.36/2.05  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 5.36/2.05  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.36/2.05  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.36/2.05  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 5.36/2.05  tff(c_58, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.36/2.05  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.36/2.05  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.36/2.05  tff(c_70, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.36/2.05  tff(c_73, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_70])).
% 5.36/2.05  tff(c_76, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_73])).
% 5.36/2.05  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.36/2.05  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.36/2.05  tff(c_1133, plain, (![C_180, A_181, B_182]: (v2_funct_1(C_180) | ~v3_funct_2(C_180, A_181, B_182) | ~v1_funct_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.36/2.05  tff(c_1142, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1133])).
% 5.36/2.05  tff(c_1149, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1142])).
% 5.36/2.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.36/2.05  tff(c_629, plain, (![C_122, B_123, A_124]: (v5_relat_1(C_122, B_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.36/2.05  tff(c_633, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_629])).
% 5.36/2.05  tff(c_646, plain, (![B_127, A_128]: (k2_relat_1(B_127)=A_128 | ~v2_funct_2(B_127, A_128) | ~v5_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.36/2.05  tff(c_649, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_633, c_646])).
% 5.36/2.05  tff(c_652, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_649])).
% 5.36/2.05  tff(c_653, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_652])).
% 5.36/2.05  tff(c_823, plain, (![C_156, B_157, A_158]: (v2_funct_2(C_156, B_157) | ~v3_funct_2(C_156, A_158, B_157) | ~v1_funct_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.36/2.05  tff(c_829, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_823])).
% 5.36/2.05  tff(c_833, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_829])).
% 5.36/2.05  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_653, c_833])).
% 5.36/2.05  tff(c_836, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_652])).
% 5.36/2.05  tff(c_858, plain, (![A_159]: (m1_subset_1(A_159, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_159), k2_relat_1(A_159)))) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.36/2.05  tff(c_870, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_836, c_858])).
% 5.36/2.05  tff(c_880, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_870])).
% 5.36/2.05  tff(c_24, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.36/2.05  tff(c_892, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_880, c_24])).
% 5.36/2.05  tff(c_14, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.36/2.05  tff(c_898, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_892, c_14])).
% 5.36/2.05  tff(c_901, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_898])).
% 5.36/2.05  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.36/2.05  tff(c_905, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_901, c_12])).
% 5.36/2.05  tff(c_909, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_836, c_905])).
% 5.36/2.05  tff(c_1237, plain, (![A_194, B_195]: (k9_relat_1(k2_funct_1(A_194), k9_relat_1(A_194, B_195))=B_195 | ~r1_tarski(B_195, k1_relat_1(A_194)) | ~v2_funct_1(A_194) | ~v1_funct_1(A_194) | ~v1_relat_1(A_194))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.36/2.05  tff(c_1267, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_909, c_1237])).
% 5.36/2.05  tff(c_1282, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_1149, c_6, c_1267])).
% 5.36/2.05  tff(c_22, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.36/2.05  tff(c_925, plain, (![A_164]: (v5_relat_1(A_164, k2_relat_1(A_164)) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(resolution, [status(thm)], [c_858, c_22])).
% 5.36/2.05  tff(c_36, plain, (![B_34]: (v2_funct_2(B_34, k2_relat_1(B_34)) | ~v5_relat_1(B_34, k2_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.36/2.05  tff(c_964, plain, (![A_167]: (v2_funct_2(A_167, k2_relat_1(A_167)) | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_925, c_36])).
% 5.36/2.05  tff(c_1454, plain, (![B_204, A_205]: (v2_funct_2(k7_relat_1(B_204, A_205), k9_relat_1(B_204, A_205)) | ~v1_funct_1(k7_relat_1(B_204, A_205)) | ~v1_relat_1(k7_relat_1(B_204, A_205)) | ~v1_relat_1(B_204))), inference(superposition, [status(thm), theory('equality')], [c_12, c_964])).
% 5.36/2.05  tff(c_1460, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1282, c_1454])).
% 5.36/2.05  tff(c_1543, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1460])).
% 5.36/2.05  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.36/2.05  tff(c_1544, plain, (![A_209, B_210]: (k2_funct_2(A_209, B_210)=k2_funct_1(B_210) | ~m1_subset_1(B_210, k1_zfmisc_1(k2_zfmisc_1(A_209, A_209))) | ~v3_funct_2(B_210, A_209, A_209) | ~v1_funct_2(B_210, A_209, A_209) | ~v1_funct_1(B_210))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.36/2.05  tff(c_1547, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1544])).
% 5.36/2.05  tff(c_1550, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1547])).
% 5.36/2.05  tff(c_1738, plain, (![A_222, B_223]: (m1_subset_1(k2_funct_2(A_222, B_223), k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~v3_funct_2(B_223, A_222, A_222) | ~v1_funct_2(B_223, A_222, A_222) | ~v1_funct_1(B_223))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/2.05  tff(c_1770, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1550, c_1738])).
% 5.36/2.05  tff(c_1785, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_1770])).
% 5.36/2.05  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.36/2.05  tff(c_1814, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1785, c_8])).
% 5.36/2.05  tff(c_1839, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1814])).
% 5.36/2.05  tff(c_1841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1543, c_1839])).
% 5.36/2.05  tff(c_1843, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1460])).
% 5.36/2.05  tff(c_3297, plain, (![A_278, B_279]: (k2_funct_2(A_278, B_279)=k2_funct_1(B_279) | ~m1_subset_1(B_279, k1_zfmisc_1(k2_zfmisc_1(A_278, A_278))) | ~v3_funct_2(B_279, A_278, A_278) | ~v1_funct_2(B_279, A_278, A_278) | ~v1_funct_1(B_279))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.36/2.05  tff(c_3300, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3297])).
% 5.36/2.05  tff(c_3303, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_3300])).
% 5.36/2.05  tff(c_1535, plain, (![A_207, B_208]: (v1_funct_1(k2_funct_2(A_207, B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~v3_funct_2(B_208, A_207, A_207) | ~v1_funct_2(B_208, A_207, A_207) | ~v1_funct_1(B_208))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/2.05  tff(c_1538, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1535])).
% 5.36/2.05  tff(c_1541, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1538])).
% 5.36/2.05  tff(c_3304, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3303, c_1541])).
% 5.36/2.05  tff(c_3466, plain, (![A_281, B_282]: (v3_funct_2(k2_funct_2(A_281, B_282), A_281, A_281) | ~m1_subset_1(B_282, k1_zfmisc_1(k2_zfmisc_1(A_281, A_281))) | ~v3_funct_2(B_282, A_281, A_281) | ~v1_funct_2(B_282, A_281, A_281) | ~v1_funct_1(B_282))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/2.05  tff(c_3468, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3466])).
% 5.36/2.05  tff(c_3471, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_3303, c_3468])).
% 5.36/2.05  tff(c_3858, plain, (![A_291, B_292]: (m1_subset_1(k2_funct_2(A_291, B_292), k1_zfmisc_1(k2_zfmisc_1(A_291, A_291))) | ~m1_subset_1(B_292, k1_zfmisc_1(k2_zfmisc_1(A_291, A_291))) | ~v3_funct_2(B_292, A_291, A_291) | ~v1_funct_2(B_292, A_291, A_291) | ~v1_funct_1(B_292))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/2.05  tff(c_3890, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3303, c_3858])).
% 5.36/2.05  tff(c_3905, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_3890])).
% 5.36/2.05  tff(c_30, plain, (![C_32, B_31, A_30]: (v2_funct_2(C_32, B_31) | ~v3_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.36/2.05  tff(c_3918, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3905, c_30])).
% 5.36/2.05  tff(c_3949, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3304, c_3471, c_3918])).
% 5.36/2.05  tff(c_3955, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_3905, c_22])).
% 5.36/2.05  tff(c_38, plain, (![B_34, A_33]: (k2_relat_1(B_34)=A_33 | ~v2_funct_2(B_34, A_33) | ~v5_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.36/2.05  tff(c_3962, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3955, c_38])).
% 5.36/2.05  tff(c_3965, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_3949, c_3962])).
% 5.36/2.05  tff(c_3956, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_3905, c_24])).
% 5.36/2.05  tff(c_3968, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3956, c_14])).
% 5.36/2.05  tff(c_3971, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_3968])).
% 5.36/2.05  tff(c_2630, plain, (![A_249, B_250]: (k2_funct_2(A_249, B_250)=k2_funct_1(B_250) | ~m1_subset_1(B_250, k1_zfmisc_1(k2_zfmisc_1(A_249, A_249))) | ~v3_funct_2(B_250, A_249, A_249) | ~v1_funct_2(B_250, A_249, A_249) | ~v1_funct_1(B_250))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.36/2.05  tff(c_2633, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2630])).
% 5.36/2.05  tff(c_2636, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2633])).
% 5.36/2.05  tff(c_3113, plain, (![A_276, B_277]: (m1_subset_1(k2_funct_2(A_276, B_277), k1_zfmisc_1(k2_zfmisc_1(A_276, A_276))) | ~m1_subset_1(B_277, k1_zfmisc_1(k2_zfmisc_1(A_276, A_276))) | ~v3_funct_2(B_277, A_276, A_276) | ~v1_funct_2(B_277, A_276, A_276) | ~v1_funct_1(B_277))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/2.05  tff(c_3145, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2636, c_3113])).
% 5.36/2.05  tff(c_3160, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_3145])).
% 5.36/2.05  tff(c_3211, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_3160, c_24])).
% 5.36/2.05  tff(c_3223, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3211, c_14])).
% 5.36/2.05  tff(c_3226, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_3223])).
% 5.36/2.05  tff(c_1865, plain, (![A_225, B_226]: (k2_funct_2(A_225, B_226)=k2_funct_1(B_226) | ~m1_subset_1(B_226, k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~v3_funct_2(B_226, A_225, A_225) | ~v1_funct_2(B_226, A_225, A_225) | ~v1_funct_1(B_226))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.36/2.05  tff(c_1868, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1865])).
% 5.36/2.05  tff(c_1871, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1868])).
% 5.36/2.05  tff(c_1872, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1871, c_1541])).
% 5.36/2.05  tff(c_2444, plain, (![A_247, B_248]: (m1_subset_1(k2_funct_2(A_247, B_248), k1_zfmisc_1(k2_zfmisc_1(A_247, A_247))) | ~m1_subset_1(B_248, k1_zfmisc_1(k2_zfmisc_1(A_247, A_247))) | ~v3_funct_2(B_248, A_247, A_247) | ~v1_funct_2(B_248, A_247, A_247) | ~v1_funct_1(B_248))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.36/2.05  tff(c_2476, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1871, c_2444])).
% 5.36/2.05  tff(c_2491, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_2476])).
% 5.36/2.05  tff(c_2542, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2491, c_24])).
% 5.36/2.05  tff(c_2554, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2542, c_14])).
% 5.36/2.05  tff(c_2557, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_2554])).
% 5.36/2.05  tff(c_1842, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1460])).
% 5.36/2.05  tff(c_1844, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_1842])).
% 5.36/2.05  tff(c_2622, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_1844])).
% 5.36/2.05  tff(c_2626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1872, c_2622])).
% 5.36/2.05  tff(c_2627, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1842])).
% 5.36/2.05  tff(c_2629, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_2627])).
% 5.36/2.05  tff(c_3290, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_2629])).
% 5.36/2.05  tff(c_3294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1843, c_3290])).
% 5.36/2.05  tff(c_3296, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'))), inference(splitRight, [status(thm)], [c_2627])).
% 5.36/2.05  tff(c_3295, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2627])).
% 5.36/2.05  tff(c_2628, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'))), inference(splitRight, [status(thm)], [c_1842])).
% 5.36/2.05  tff(c_1401, plain, (![B_202, A_203]: (v5_relat_1(k7_relat_1(B_202, A_203), k9_relat_1(B_202, A_203)) | ~v1_funct_1(k7_relat_1(B_202, A_203)) | ~v1_relat_1(k7_relat_1(B_202, A_203)) | ~v1_relat_1(B_202))), inference(superposition, [status(thm), theory('equality')], [c_12, c_925])).
% 5.36/2.05  tff(c_1410, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1282, c_1401])).
% 5.36/2.05  tff(c_3310, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_3296, c_2628, c_1410])).
% 5.36/2.05  tff(c_3313, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'))), inference(resolution, [status(thm)], [c_3310, c_38])).
% 5.36/2.05  tff(c_3316, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3296, c_3295, c_3313])).
% 5.36/2.05  tff(c_4044, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3971, c_3316])).
% 5.36/2.05  tff(c_4050, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_4044])).
% 5.36/2.05  tff(c_595, plain, (![C_115, A_116, B_117]: (v4_relat_1(C_115, A_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.36/2.05  tff(c_599, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_595])).
% 5.36/2.05  tff(c_609, plain, (![B_120, A_121]: (k7_relat_1(B_120, A_121)=B_120 | ~v4_relat_1(B_120, A_121) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.36/2.05  tff(c_612, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_599, c_609])).
% 5.36/2.05  tff(c_615, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_612])).
% 5.36/2.05  tff(c_619, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_615, c_12])).
% 5.36/2.05  tff(c_623, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_619])).
% 5.36/2.05  tff(c_838, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_836, c_623])).
% 5.36/2.05  tff(c_1270, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_838, c_1237])).
% 5.36/2.05  tff(c_1284, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_1149, c_1270])).
% 5.36/2.05  tff(c_1292, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1282, c_1284])).
% 5.36/2.05  tff(c_1293, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1292])).
% 5.36/2.05  tff(c_4075, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4050, c_1293])).
% 5.36/2.05  tff(c_4086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4075])).
% 5.36/2.05  tff(c_4087, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1292])).
% 5.36/2.05  tff(c_18, plain, (![B_15, A_14]: (k10_relat_1(B_15, k9_relat_1(B_15, A_14))=A_14 | ~v2_funct_1(B_15) | ~r1_tarski(A_14, k1_relat_1(B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.36/2.05  tff(c_4113, plain, (![A_14]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_14))=A_14 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_14, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4087, c_18])).
% 5.36/2.05  tff(c_4169, plain, (![A_295]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_295))=A_295 | ~r1_tarski(A_295, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_1149, c_4113])).
% 5.36/2.05  tff(c_1095, plain, (![A_175, B_176, C_177, D_178]: (k8_relset_1(A_175, B_176, C_177, D_178)=k10_relat_1(C_177, D_178) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.36/2.05  tff(c_1104, plain, (![D_178]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_178)=k10_relat_1('#skF_3', D_178))), inference(resolution, [status(thm)], [c_60, c_1095])).
% 5.36/2.05  tff(c_911, plain, (![A_160, B_161, C_162, D_163]: (k7_relset_1(A_160, B_161, C_162, D_163)=k9_relat_1(C_162, D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.36/2.05  tff(c_920, plain, (![D_163]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_163)=k9_relat_1('#skF_3', D_163))), inference(resolution, [status(thm)], [c_60, c_911])).
% 5.36/2.05  tff(c_98, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.36/2.05  tff(c_102, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_98])).
% 5.36/2.05  tff(c_136, plain, (![B_59, A_60]: (k2_relat_1(B_59)=A_60 | ~v2_funct_2(B_59, A_60) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.36/2.05  tff(c_139, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_136])).
% 5.36/2.05  tff(c_142, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_139])).
% 5.36/2.05  tff(c_161, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_142])).
% 5.36/2.05  tff(c_285, plain, (![C_86, B_87, A_88]: (v2_funct_2(C_86, B_87) | ~v3_funct_2(C_86, A_88, B_87) | ~v1_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.36/2.05  tff(c_291, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_285])).
% 5.36/2.05  tff(c_295, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_291])).
% 5.36/2.05  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_295])).
% 5.36/2.05  tff(c_298, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_142])).
% 5.36/2.05  tff(c_359, plain, (![B_89, A_90]: (k9_relat_1(B_89, k10_relat_1(B_89, A_90))=A_90 | ~r1_tarski(A_90, k2_relat_1(B_89)) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.05  tff(c_361, plain, (![A_90]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_90))=A_90 | ~r1_tarski(A_90, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_298, c_359])).
% 5.36/2.05  tff(c_368, plain, (![A_90]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_90))=A_90 | ~r1_tarski(A_90, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_66, c_361])).
% 5.36/2.05  tff(c_555, plain, (![A_108, B_109, C_110, D_111]: (k8_relset_1(A_108, B_109, C_110, D_111)=k10_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.36/2.05  tff(c_564, plain, (![D_111]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_111)=k10_relat_1('#skF_3', D_111))), inference(resolution, [status(thm)], [c_60, c_555])).
% 5.36/2.05  tff(c_516, plain, (![A_101, B_102, C_103, D_104]: (k7_relset_1(A_101, B_102, C_103, D_104)=k9_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.36/2.05  tff(c_525, plain, (![D_104]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_104)=k9_relat_1('#skF_3', D_104))), inference(resolution, [status(thm)], [c_60, c_516])).
% 5.36/2.05  tff(c_56, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.36/2.05  tff(c_77, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 5.36/2.05  tff(c_527, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_525, c_77])).
% 5.36/2.05  tff(c_565, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_564, c_527])).
% 5.36/2.05  tff(c_577, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_368, c_565])).
% 5.36/2.05  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_577])).
% 5.36/2.05  tff(c_582, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 5.36/2.05  tff(c_948, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_920, c_582])).
% 5.36/2.05  tff(c_1106, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_948])).
% 5.36/2.05  tff(c_4175, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4169, c_1106])).
% 5.36/2.05  tff(c_4206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_4175])).
% 5.36/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.36/2.05  
% 5.36/2.05  Inference rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Ref     : 0
% 5.36/2.05  #Sup     : 901
% 5.36/2.05  #Fact    : 0
% 5.36/2.05  #Define  : 0
% 5.36/2.05  #Split   : 20
% 5.36/2.05  #Chain   : 0
% 5.36/2.05  #Close   : 0
% 5.36/2.05  
% 5.36/2.05  Ordering : KBO
% 5.36/2.05  
% 5.36/2.05  Simplification rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Subsume      : 38
% 5.36/2.05  #Demod        : 2075
% 5.36/2.05  #Tautology    : 386
% 5.36/2.05  #SimpNegUnit  : 6
% 5.36/2.05  #BackRed      : 75
% 5.36/2.05  
% 5.36/2.05  #Partial instantiations: 0
% 5.36/2.05  #Strategies tried      : 1
% 5.36/2.05  
% 5.36/2.05  Timing (in seconds)
% 5.36/2.05  ----------------------
% 5.36/2.05  Preprocessing        : 0.35
% 5.36/2.05  Parsing              : 0.19
% 5.36/2.05  CNF conversion       : 0.02
% 5.36/2.05  Main loop            : 0.91
% 5.36/2.05  Inferencing          : 0.32
% 5.36/2.05  Reduction            : 0.33
% 5.36/2.05  Demodulation         : 0.25
% 5.36/2.05  BG Simplification    : 0.04
% 5.36/2.05  Subsumption          : 0.15
% 5.36/2.06  Abstraction          : 0.04
% 5.36/2.06  MUC search           : 0.00
% 5.36/2.06  Cooper               : 0.00
% 5.36/2.06  Total                : 1.33
% 5.36/2.06  Index Insertion      : 0.00
% 5.36/2.06  Index Deletion       : 0.00
% 5.36/2.06  Index Matching       : 0.00
% 5.36/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
