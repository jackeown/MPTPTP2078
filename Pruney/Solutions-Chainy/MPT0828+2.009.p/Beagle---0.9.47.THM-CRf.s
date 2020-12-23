%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:18 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   92 ( 152 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_454,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_relset_1(A_95,B_96,C_97) = k2_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_463,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_454])).

tff(c_104,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_113,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_104])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_114,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_66])).

tff(c_67,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_32,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_relat_1(A_48),k1_relat_1(B_49))
      | ~ r1_tarski(A_48,B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_144,plain,(
    ! [A_9,B_49] :
      ( r1_tarski(A_9,k1_relat_1(B_49))
      | ~ r1_tarski(k6_relat_1(A_9),B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_139])).

tff(c_153,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,k1_relat_1(B_51))
      | ~ r1_tarski(k6_relat_1(A_50),B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_144])).

tff(c_156,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_153])).

tff(c_163,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_156])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_171,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_168])).

tff(c_341,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k1_relset_1(A_76,B_77,C_78),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_362,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_341])).

tff(c_368,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_362])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_371,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_368,c_8])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_371])).

tff(c_376,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_464,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_376])).

tff(c_396,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_405,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_396])).

tff(c_20,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_693,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(k2_relat_1(A_126),k2_relat_1(B_127))
      | ~ r1_tarski(A_126,B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_698,plain,(
    ! [A_9,B_127] :
      ( r1_tarski(A_9,k2_relat_1(B_127))
      | ~ r1_tarski(k6_relat_1(A_9),B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_693])).

tff(c_707,plain,(
    ! [A_128,B_129] :
      ( r1_tarski(A_128,k2_relat_1(B_129))
      | ~ r1_tarski(k6_relat_1(A_128),B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_698])).

tff(c_710,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_707])).

tff(c_717,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_710])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_464,c_717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.47  
% 2.62/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.47  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.47  
% 2.62/1.47  %Foreground sorts:
% 2.62/1.47  
% 2.62/1.47  
% 2.62/1.47  %Background operators:
% 2.62/1.47  
% 2.62/1.47  
% 2.62/1.47  %Foreground operators:
% 2.62/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.62/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.47  
% 2.62/1.48  tff(f_77, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.62/1.48  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.62/1.48  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.62/1.48  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.48  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.62/1.48  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.62/1.48  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.62/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.62/1.48  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.62/1.48  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.62/1.48  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.48  tff(c_454, plain, (![A_95, B_96, C_97]: (k2_relset_1(A_95, B_96, C_97)=k2_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.62/1.48  tff(c_463, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_454])).
% 2.62/1.48  tff(c_104, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.62/1.48  tff(c_113, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_104])).
% 2.62/1.48  tff(c_30, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.48  tff(c_66, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.62/1.48  tff(c_114, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_66])).
% 2.62/1.48  tff(c_67, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.48  tff(c_76, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.62/1.48  tff(c_32, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.48  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.48  tff(c_18, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.62/1.48  tff(c_139, plain, (![A_48, B_49]: (r1_tarski(k1_relat_1(A_48), k1_relat_1(B_49)) | ~r1_tarski(A_48, B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.62/1.48  tff(c_144, plain, (![A_9, B_49]: (r1_tarski(A_9, k1_relat_1(B_49)) | ~r1_tarski(k6_relat_1(A_9), B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_139])).
% 2.62/1.48  tff(c_153, plain, (![A_50, B_51]: (r1_tarski(A_50, k1_relat_1(B_51)) | ~r1_tarski(k6_relat_1(A_50), B_51) | ~v1_relat_1(B_51))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_144])).
% 2.62/1.48  tff(c_156, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_153])).
% 2.62/1.48  tff(c_163, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_156])).
% 2.62/1.48  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.48  tff(c_168, plain, (k1_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_163, c_2])).
% 2.62/1.48  tff(c_171, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_114, c_168])).
% 2.62/1.48  tff(c_341, plain, (![A_76, B_77, C_78]: (m1_subset_1(k1_relset_1(A_76, B_77, C_78), k1_zfmisc_1(A_76)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.48  tff(c_362, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_113, c_341])).
% 2.62/1.48  tff(c_368, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_362])).
% 2.62/1.48  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.48  tff(c_371, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_368, c_8])).
% 2.62/1.48  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_371])).
% 2.62/1.48  tff(c_376, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.62/1.48  tff(c_464, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_376])).
% 2.62/1.48  tff(c_396, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.62/1.48  tff(c_405, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_396])).
% 2.62/1.48  tff(c_20, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.62/1.48  tff(c_693, plain, (![A_126, B_127]: (r1_tarski(k2_relat_1(A_126), k2_relat_1(B_127)) | ~r1_tarski(A_126, B_127) | ~v1_relat_1(B_127) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.62/1.48  tff(c_698, plain, (![A_9, B_127]: (r1_tarski(A_9, k2_relat_1(B_127)) | ~r1_tarski(k6_relat_1(A_9), B_127) | ~v1_relat_1(B_127) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_693])).
% 2.62/1.48  tff(c_707, plain, (![A_128, B_129]: (r1_tarski(A_128, k2_relat_1(B_129)) | ~r1_tarski(k6_relat_1(A_128), B_129) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_698])).
% 2.62/1.48  tff(c_710, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_707])).
% 2.62/1.48  tff(c_717, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_710])).
% 2.62/1.48  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_464, c_717])).
% 2.62/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.48  
% 2.62/1.48  Inference rules
% 2.62/1.48  ----------------------
% 2.62/1.48  #Ref     : 0
% 2.62/1.48  #Sup     : 135
% 2.62/1.48  #Fact    : 0
% 2.62/1.48  #Define  : 0
% 2.62/1.48  #Split   : 7
% 2.62/1.48  #Chain   : 0
% 2.62/1.48  #Close   : 0
% 2.62/1.48  
% 2.62/1.48  Ordering : KBO
% 2.62/1.48  
% 2.62/1.48  Simplification rules
% 2.62/1.48  ----------------------
% 2.62/1.48  #Subsume      : 5
% 2.62/1.48  #Demod        : 88
% 2.62/1.48  #Tautology    : 52
% 2.62/1.48  #SimpNegUnit  : 3
% 2.62/1.48  #BackRed      : 4
% 2.62/1.48  
% 2.62/1.48  #Partial instantiations: 0
% 2.62/1.48  #Strategies tried      : 1
% 2.62/1.48  
% 2.62/1.48  Timing (in seconds)
% 2.62/1.48  ----------------------
% 2.62/1.49  Preprocessing        : 0.28
% 2.62/1.49  Parsing              : 0.14
% 2.62/1.49  CNF conversion       : 0.02
% 2.62/1.49  Main loop            : 0.32
% 2.62/1.49  Inferencing          : 0.12
% 2.62/1.49  Reduction            : 0.10
% 2.62/1.49  Demodulation         : 0.07
% 2.62/1.49  BG Simplification    : 0.02
% 2.62/1.49  Subsumption          : 0.06
% 2.62/1.49  Abstraction          : 0.02
% 2.62/1.49  MUC search           : 0.00
% 2.62/1.49  Cooper               : 0.00
% 2.62/1.49  Total                : 0.63
% 2.62/1.49  Index Insertion      : 0.00
% 2.62/1.49  Index Deletion       : 0.00
% 2.62/1.49  Index Matching       : 0.00
% 2.62/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
