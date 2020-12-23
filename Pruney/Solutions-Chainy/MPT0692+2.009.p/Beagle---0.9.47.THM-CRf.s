%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:51 EST 2020

% Result     : Theorem 54.00s
% Output     : CNFRefutation 54.12s
% Verified   : 
% Statistics : Number of formulae       :   51 (  57 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 112 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(A,k2_relat_1(B))
         => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_26,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k10_relat_1(B_11,A_10),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [C_16,A_14,B_15] :
      ( k6_subset_1(k10_relat_1(C_16,A_14),k10_relat_1(C_16,B_15)) = k10_relat_1(C_16,k6_subset_1(A_14,B_15))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    ! [C_16,A_14,B_15] :
      ( k4_xboole_0(k10_relat_1(C_16,A_14),k10_relat_1(C_16,B_15)) = k10_relat_1(C_16,k4_xboole_0(A_14,B_15))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_369,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,k10_relat_1(B_57,k9_relat_1(B_57,A_56)))
      | ~ r1_tarski(A_56,k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1568,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,k10_relat_1(B_98,k9_relat_1(B_98,A_97))) = k1_xboole_0
      | ~ r1_tarski(A_97,k1_relat_1(B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_369,c_10])).

tff(c_22774,plain,(
    ! [C_358,A_359] :
      ( k10_relat_1(C_358,k4_xboole_0(A_359,k9_relat_1(C_358,k10_relat_1(C_358,A_359)))) = k1_xboole_0
      | ~ r1_tarski(k10_relat_1(C_358,A_359),k1_relat_1(C_358))
      | ~ v1_relat_1(C_358)
      | ~ v1_funct_1(C_358)
      | ~ v1_relat_1(C_358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_1568])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_239,plain,(
    ! [B_47,A_48] :
      ( k10_relat_1(B_47,A_48) != k1_xboole_0
      | ~ r1_tarski(A_48,k2_relat_1(B_47))
      | k1_xboole_0 = A_48
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_266,plain,(
    ! [B_47,A_5,C_7] :
      ( k10_relat_1(B_47,k4_xboole_0(A_5,C_7)) != k1_xboole_0
      | k4_xboole_0(A_5,C_7) = k1_xboole_0
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(A_5,k2_relat_1(B_47)) ) ),
    inference(resolution,[status(thm)],[c_12,c_239])).

tff(c_98152,plain,(
    ! [A_853,C_854] :
      ( k4_xboole_0(A_853,k9_relat_1(C_854,k10_relat_1(C_854,A_853))) = k1_xboole_0
      | ~ r1_tarski(A_853,k2_relat_1(C_854))
      | ~ r1_tarski(k10_relat_1(C_854,A_853),k1_relat_1(C_854))
      | ~ v1_funct_1(C_854)
      | ~ v1_relat_1(C_854) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22774,c_266])).

tff(c_259490,plain,(
    ! [A_1356,B_1357] :
      ( k4_xboole_0(A_1356,k9_relat_1(B_1357,k10_relat_1(B_1357,A_1356))) = k1_xboole_0
      | ~ r1_tarski(A_1356,k2_relat_1(B_1357))
      | ~ v1_funct_1(B_1357)
      | ~ v1_relat_1(B_1357) ) ),
    inference(resolution,[status(thm)],[c_16,c_98152])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,k10_relat_1(B_18,A_17)),A_17)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | k4_xboole_0(A_55,B_54) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_359,plain,(
    ! [B_18,A_17] :
      ( k9_relat_1(B_18,k10_relat_1(B_18,A_17)) = A_17
      | k4_xboole_0(A_17,k9_relat_1(B_18,k10_relat_1(B_18,A_17))) != k1_xboole_0
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_22,c_337])).

tff(c_261425,plain,(
    ! [B_1358,A_1359] :
      ( k9_relat_1(B_1358,k10_relat_1(B_1358,A_1359)) = A_1359
      | ~ r1_tarski(A_1359,k2_relat_1(B_1358))
      | ~ v1_funct_1(B_1358)
      | ~ v1_relat_1(B_1358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259490,c_359])).

tff(c_261466,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_261425])).

tff(c_261485,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_261466])).

tff(c_261487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_261485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:36:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 54.00/44.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.00/44.41  
% 54.00/44.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.00/44.41  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 54.00/44.41  
% 54.00/44.41  %Foreground sorts:
% 54.00/44.41  
% 54.00/44.41  
% 54.00/44.41  %Background operators:
% 54.00/44.41  
% 54.00/44.41  
% 54.00/44.41  %Foreground operators:
% 54.00/44.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 54.00/44.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 54.00/44.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 54.00/44.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 54.00/44.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 54.00/44.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 54.00/44.41  tff('#skF_2', type, '#skF_2': $i).
% 54.00/44.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 54.00/44.41  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 54.00/44.41  tff('#skF_1', type, '#skF_1': $i).
% 54.00/44.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 54.00/44.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 54.00/44.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 54.00/44.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 54.00/44.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 54.00/44.41  
% 54.12/44.42  tff(f_82, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 54.12/44.42  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 54.12/44.42  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 54.12/44.42  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 54.12/44.42  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 54.12/44.42  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 54.12/44.42  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 54.12/44.42  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 54.12/44.42  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 54.12/44.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 54.12/44.42  tff(c_26, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 54.12/44.42  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 54.12/44.42  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 54.12/44.42  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 54.12/44.42  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k10_relat_1(B_11, A_10), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 54.12/44.42  tff(c_14, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 54.12/44.42  tff(c_20, plain, (![C_16, A_14, B_15]: (k6_subset_1(k10_relat_1(C_16, A_14), k10_relat_1(C_16, B_15))=k10_relat_1(C_16, k6_subset_1(A_14, B_15)) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 54.12/44.42  tff(c_33, plain, (![C_16, A_14, B_15]: (k4_xboole_0(k10_relat_1(C_16, A_14), k10_relat_1(C_16, B_15))=k10_relat_1(C_16, k4_xboole_0(A_14, B_15)) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 54.12/44.42  tff(c_369, plain, (![A_56, B_57]: (r1_tarski(A_56, k10_relat_1(B_57, k9_relat_1(B_57, A_56))) | ~r1_tarski(A_56, k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 54.12/44.42  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 54.12/44.42  tff(c_1568, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k10_relat_1(B_98, k9_relat_1(B_98, A_97)))=k1_xboole_0 | ~r1_tarski(A_97, k1_relat_1(B_98)) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_369, c_10])).
% 54.12/44.42  tff(c_22774, plain, (![C_358, A_359]: (k10_relat_1(C_358, k4_xboole_0(A_359, k9_relat_1(C_358, k10_relat_1(C_358, A_359))))=k1_xboole_0 | ~r1_tarski(k10_relat_1(C_358, A_359), k1_relat_1(C_358)) | ~v1_relat_1(C_358) | ~v1_funct_1(C_358) | ~v1_relat_1(C_358))), inference(superposition, [status(thm), theory('equality')], [c_33, c_1568])).
% 54.12/44.42  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 54.12/44.42  tff(c_239, plain, (![B_47, A_48]: (k10_relat_1(B_47, A_48)!=k1_xboole_0 | ~r1_tarski(A_48, k2_relat_1(B_47)) | k1_xboole_0=A_48 | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 54.12/44.42  tff(c_266, plain, (![B_47, A_5, C_7]: (k10_relat_1(B_47, k4_xboole_0(A_5, C_7))!=k1_xboole_0 | k4_xboole_0(A_5, C_7)=k1_xboole_0 | ~v1_relat_1(B_47) | ~r1_tarski(A_5, k2_relat_1(B_47)))), inference(resolution, [status(thm)], [c_12, c_239])).
% 54.12/44.42  tff(c_98152, plain, (![A_853, C_854]: (k4_xboole_0(A_853, k9_relat_1(C_854, k10_relat_1(C_854, A_853)))=k1_xboole_0 | ~r1_tarski(A_853, k2_relat_1(C_854)) | ~r1_tarski(k10_relat_1(C_854, A_853), k1_relat_1(C_854)) | ~v1_funct_1(C_854) | ~v1_relat_1(C_854))), inference(superposition, [status(thm), theory('equality')], [c_22774, c_266])).
% 54.12/44.42  tff(c_259490, plain, (![A_1356, B_1357]: (k4_xboole_0(A_1356, k9_relat_1(B_1357, k10_relat_1(B_1357, A_1356)))=k1_xboole_0 | ~r1_tarski(A_1356, k2_relat_1(B_1357)) | ~v1_funct_1(B_1357) | ~v1_relat_1(B_1357))), inference(resolution, [status(thm)], [c_16, c_98152])).
% 54.12/44.42  tff(c_22, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, k10_relat_1(B_18, A_17)), A_17) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 54.12/44.42  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 54.12/44.42  tff(c_70, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 54.12/44.42  tff(c_337, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | k4_xboole_0(A_55, B_54)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_70])).
% 54.12/44.42  tff(c_359, plain, (![B_18, A_17]: (k9_relat_1(B_18, k10_relat_1(B_18, A_17))=A_17 | k4_xboole_0(A_17, k9_relat_1(B_18, k10_relat_1(B_18, A_17)))!=k1_xboole_0 | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_22, c_337])).
% 54.12/44.42  tff(c_261425, plain, (![B_1358, A_1359]: (k9_relat_1(B_1358, k10_relat_1(B_1358, A_1359))=A_1359 | ~r1_tarski(A_1359, k2_relat_1(B_1358)) | ~v1_funct_1(B_1358) | ~v1_relat_1(B_1358))), inference(superposition, [status(thm), theory('equality')], [c_259490, c_359])).
% 54.12/44.42  tff(c_261466, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_261425])).
% 54.12/44.42  tff(c_261485, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_261466])).
% 54.12/44.42  tff(c_261487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_261485])).
% 54.12/44.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 54.12/44.42  
% 54.12/44.42  Inference rules
% 54.12/44.42  ----------------------
% 54.12/44.42  #Ref     : 0
% 54.12/44.42  #Sup     : 62871
% 54.12/44.42  #Fact    : 0
% 54.12/44.42  #Define  : 0
% 54.12/44.42  #Split   : 9
% 54.12/44.42  #Chain   : 0
% 54.12/44.42  #Close   : 0
% 54.12/44.42  
% 54.12/44.42  Ordering : KBO
% 54.12/44.42  
% 54.12/44.42  Simplification rules
% 54.12/44.42  ----------------------
% 54.12/44.42  #Subsume      : 13137
% 54.12/44.42  #Demod        : 115158
% 54.12/44.42  #Tautology    : 35296
% 54.12/44.42  #SimpNegUnit  : 204
% 54.12/44.42  #BackRed      : 0
% 54.12/44.42  
% 54.12/44.42  #Partial instantiations: 0
% 54.12/44.42  #Strategies tried      : 1
% 54.12/44.42  
% 54.12/44.42  Timing (in seconds)
% 54.12/44.42  ----------------------
% 54.12/44.43  Preprocessing        : 0.28
% 54.12/44.43  Parsing              : 0.15
% 54.12/44.43  CNF conversion       : 0.02
% 54.12/44.43  Main loop            : 43.40
% 54.12/44.43  Inferencing          : 4.57
% 54.12/44.43  Reduction            : 15.58
% 54.12/44.43  Demodulation         : 12.81
% 54.12/44.43  BG Simplification    : 0.61
% 54.12/44.43  Subsumption          : 21.33
% 54.12/44.43  Abstraction          : 1.10
% 54.12/44.43  MUC search           : 0.00
% 54.12/44.43  Cooper               : 0.00
% 54.12/44.43  Total                : 43.71
% 54.12/44.43  Index Insertion      : 0.00
% 54.12/44.43  Index Deletion       : 0.00
% 54.12/44.43  Index Matching       : 0.00
% 54.12/44.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
