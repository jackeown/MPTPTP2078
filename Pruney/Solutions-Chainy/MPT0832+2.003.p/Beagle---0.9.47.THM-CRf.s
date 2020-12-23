%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:40 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 127 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_41,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_9,B_10)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k8_relat_1(A_11,B_12),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_101,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39,c_101])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [A_4,A_40,B_41] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_40,B_41)) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_140,plain,(
    ! [A_60] :
      ( v1_relat_1(A_60)
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_128,c_49])).

tff(c_148,plain,(
    ! [A_11] :
      ( v1_relat_1(k8_relat_1(A_11,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_152,plain,(
    ! [A_11] : v1_relat_1(k8_relat_1(A_11,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_148])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_13,B_14)),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_114,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_157,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k1_relset_1(A_68,B_69,C_70),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_174,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_157])).

tff(c_180,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,'#skF_3')
      | ~ r1_tarski(A_73,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_188,c_2])).

tff(c_221,plain,(
    ! [A_13] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_13,'#skF_4')),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_217])).

tff(c_232,plain,(
    ! [A_13] : r1_tarski(k1_relat_1(k8_relat_1(A_13,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_221])).

tff(c_315,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ r1_tarski(k2_relat_1(C_85),B_87)
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_247,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k6_relset_1(A_75,B_76,C_77,D_78) = k8_relat_1(C_77,D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_258,plain,(
    ! [C_77] : k6_relset_1('#skF_3','#skF_1',C_77,'#skF_4') = k8_relat_1(C_77,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_247])).

tff(c_26,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_260,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_26])).

tff(c_318,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_315,c_260])).

tff(c_335,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_232,c_318])).

tff(c_343,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_335])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  
% 2.31/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.31  
% 2.31/1.31  %Foreground sorts:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Background operators:
% 2.31/1.31  
% 2.31/1.31  
% 2.31/1.31  %Foreground operators:
% 2.31/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.31  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.31/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.31/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.31  
% 2.31/1.33  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.31/1.33  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.31/1.33  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.31/1.33  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.31/1.33  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.31/1.33  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.31/1.33  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_wellord1)).
% 2.31/1.33  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.31/1.33  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.31/1.33  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.31/1.33  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.31/1.33  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.31/1.33  tff(c_41, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.31/1.33  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.31/1.33  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k2_relat_1(k8_relat_1(A_9, B_10)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.33  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k8_relat_1(A_11, B_12), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.31/1.33  tff(c_31, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.33  tff(c_39, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.31/1.33  tff(c_101, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.33  tff(c_128, plain, (![A_59]: (r1_tarski(A_59, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_59, '#skF_4'))), inference(resolution, [status(thm)], [c_39, c_101])).
% 2.31/1.33  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.33  tff(c_49, plain, (![A_4, A_40, B_41]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_40, B_41)))), inference(resolution, [status(thm)], [c_6, c_41])).
% 2.31/1.33  tff(c_140, plain, (![A_60]: (v1_relat_1(A_60) | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_128, c_49])).
% 2.31/1.33  tff(c_148, plain, (![A_11]: (v1_relat_1(k8_relat_1(A_11, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_140])).
% 2.31/1.33  tff(c_152, plain, (![A_11]: (v1_relat_1(k8_relat_1(A_11, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_148])).
% 2.31/1.33  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k1_relat_1(k8_relat_1(A_13, B_14)), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.31/1.33  tff(c_114, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.33  tff(c_123, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.31/1.33  tff(c_157, plain, (![A_68, B_69, C_70]: (m1_subset_1(k1_relset_1(A_68, B_69, C_70), k1_zfmisc_1(A_68)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.33  tff(c_174, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_157])).
% 2.31/1.33  tff(c_180, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_174])).
% 2.31/1.33  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.33  tff(c_188, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_180, c_4])).
% 2.31/1.33  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.33  tff(c_217, plain, (![A_73]: (r1_tarski(A_73, '#skF_3') | ~r1_tarski(A_73, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_188, c_2])).
% 2.31/1.33  tff(c_221, plain, (![A_13]: (r1_tarski(k1_relat_1(k8_relat_1(A_13, '#skF_4')), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_217])).
% 2.31/1.33  tff(c_232, plain, (![A_13]: (r1_tarski(k1_relat_1(k8_relat_1(A_13, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_221])).
% 2.31/1.33  tff(c_315, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~r1_tarski(k2_relat_1(C_85), B_87) | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.31/1.33  tff(c_247, plain, (![A_75, B_76, C_77, D_78]: (k6_relset_1(A_75, B_76, C_77, D_78)=k8_relat_1(C_77, D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.33  tff(c_258, plain, (![C_77]: (k6_relset_1('#skF_3', '#skF_1', C_77, '#skF_4')=k8_relat_1(C_77, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_247])).
% 2.31/1.33  tff(c_26, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.31/1.33  tff(c_260, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_26])).
% 2.31/1.33  tff(c_318, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_315, c_260])).
% 2.31/1.33  tff(c_335, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_232, c_318])).
% 2.31/1.33  tff(c_343, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_335])).
% 2.31/1.33  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_343])).
% 2.31/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  Inference rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Ref     : 0
% 2.31/1.33  #Sup     : 70
% 2.31/1.33  #Fact    : 0
% 2.31/1.33  #Define  : 0
% 2.31/1.33  #Split   : 3
% 2.31/1.33  #Chain   : 0
% 2.31/1.33  #Close   : 0
% 2.31/1.33  
% 2.31/1.33  Ordering : KBO
% 2.31/1.33  
% 2.31/1.33  Simplification rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Subsume      : 9
% 2.31/1.33  #Demod        : 13
% 2.31/1.33  #Tautology    : 11
% 2.31/1.33  #SimpNegUnit  : 0
% 2.31/1.33  #BackRed      : 2
% 2.31/1.33  
% 2.31/1.33  #Partial instantiations: 0
% 2.31/1.33  #Strategies tried      : 1
% 2.31/1.33  
% 2.31/1.33  Timing (in seconds)
% 2.31/1.33  ----------------------
% 2.31/1.33  Preprocessing        : 0.30
% 2.31/1.33  Parsing              : 0.17
% 2.31/1.33  CNF conversion       : 0.02
% 2.31/1.33  Main loop            : 0.24
% 2.31/1.33  Inferencing          : 0.09
% 2.31/1.33  Reduction            : 0.06
% 2.31/1.33  Demodulation         : 0.05
% 2.31/1.33  BG Simplification    : 0.01
% 2.31/1.33  Subsumption          : 0.05
% 2.31/1.33  Abstraction          : 0.01
% 2.31/1.33  MUC search           : 0.00
% 2.31/1.33  Cooper               : 0.00
% 2.31/1.33  Total                : 0.57
% 2.31/1.33  Index Insertion      : 0.00
% 2.31/1.33  Index Deletion       : 0.00
% 2.31/1.33  Index Matching       : 0.00
% 2.31/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
