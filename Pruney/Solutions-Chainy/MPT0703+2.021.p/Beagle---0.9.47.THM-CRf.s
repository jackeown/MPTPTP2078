%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   50 (  58 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 100 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( k6_subset_1(k10_relat_1(C_20,A_18),k10_relat_1(C_20,B_19)) = k10_relat_1(C_20,k6_subset_1(A_18,B_19))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_796,plain,(
    ! [C_70,A_71,B_72] :
      ( k4_xboole_0(k10_relat_1(C_70,A_71),k10_relat_1(C_70,B_72)) = k10_relat_1(C_70,k4_xboole_0(A_71,B_72))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_47,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_47])).

tff(c_823,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_57])).

tff(c_842,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_823])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_194,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(k2_relat_1(B_42),A_43)
      | k10_relat_1(B_42,A_43) != k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_xboole_0(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1751,plain,(
    ! [A_102,A_103,B_104] :
      ( r1_xboole_0(A_102,A_103)
      | ~ r1_tarski(A_102,k2_relat_1(B_104))
      | k10_relat_1(B_104,A_103) != k1_xboole_0
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_194,c_14])).

tff(c_1756,plain,(
    ! [A_103] :
      ( r1_xboole_0('#skF_1',A_103)
      | k10_relat_1('#skF_3',A_103) != k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_1751])).

tff(c_1765,plain,(
    ! [A_105] :
      ( r1_xboole_0('#skF_1',A_105)
      | k10_relat_1('#skF_3',A_105) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1756])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(A_36,k2_xboole_0(B_37,C_38))
      | ~ r1_tarski(k4_xboole_0(A_36,B_37),C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,(
    ! [A_36,B_37] : r1_tarski(A_36,k2_xboole_0(B_37,k4_xboole_0(A_36,B_37))) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_494,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,B_61)
      | ~ r1_xboole_0(A_60,C_62)
      | ~ r1_tarski(A_60,k2_xboole_0(B_61,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_555,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ r1_xboole_0(A_36,k4_xboole_0(A_36,B_37)) ) ),
    inference(resolution,[status(thm)],[c_150,c_494])).

tff(c_1779,plain,(
    ! [B_106] :
      ( r1_tarski('#skF_1',B_106)
      | k10_relat_1('#skF_3',k4_xboole_0('#skF_1',B_106)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1765,c_555])).

tff(c_1801,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_1779])).

tff(c_1851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.71  
% 3.67/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.71  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.67/1.71  
% 3.67/1.71  %Foreground sorts:
% 3.67/1.71  
% 3.67/1.71  
% 3.67/1.71  %Background operators:
% 3.67/1.71  
% 3.67/1.71  
% 3.67/1.71  %Foreground operators:
% 3.67/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.67/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.67/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.67/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.67/1.71  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.67/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.67/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.67/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.71  
% 3.67/1.72  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.67/1.72  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.67/1.72  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 3.67/1.72  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.67/1.72  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.67/1.72  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.67/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.67/1.72  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.67/1.72  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 3.67/1.72  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.67/1.72  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.67/1.72  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.67/1.72  tff(c_18, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.67/1.72  tff(c_24, plain, (![C_20, A_18, B_19]: (k6_subset_1(k10_relat_1(C_20, A_18), k10_relat_1(C_20, B_19))=k10_relat_1(C_20, k6_subset_1(A_18, B_19)) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.67/1.72  tff(c_796, plain, (![C_70, A_71, B_72]: (k4_xboole_0(k10_relat_1(C_70, A_71), k10_relat_1(C_70, B_72))=k10_relat_1(C_70, k4_xboole_0(A_71, B_72)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 3.67/1.72  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.67/1.72  tff(c_47, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.67/1.72  tff(c_57, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_47])).
% 3.67/1.72  tff(c_823, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_796, c_57])).
% 3.67/1.72  tff(c_842, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_823])).
% 3.67/1.72  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.67/1.72  tff(c_194, plain, (![B_42, A_43]: (r1_xboole_0(k2_relat_1(B_42), A_43) | k10_relat_1(B_42, A_43)!=k1_xboole_0 | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.67/1.72  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_xboole_0(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.67/1.72  tff(c_1751, plain, (![A_102, A_103, B_104]: (r1_xboole_0(A_102, A_103) | ~r1_tarski(A_102, k2_relat_1(B_104)) | k10_relat_1(B_104, A_103)!=k1_xboole_0 | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_194, c_14])).
% 3.67/1.73  tff(c_1756, plain, (![A_103]: (r1_xboole_0('#skF_1', A_103) | k10_relat_1('#skF_3', A_103)!=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_1751])).
% 3.67/1.73  tff(c_1765, plain, (![A_105]: (r1_xboole_0('#skF_1', A_105) | k10_relat_1('#skF_3', A_105)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1756])).
% 3.67/1.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.67/1.73  tff(c_131, plain, (![A_36, B_37, C_38]: (r1_tarski(A_36, k2_xboole_0(B_37, C_38)) | ~r1_tarski(k4_xboole_0(A_36, B_37), C_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.67/1.73  tff(c_150, plain, (![A_36, B_37]: (r1_tarski(A_36, k2_xboole_0(B_37, k4_xboole_0(A_36, B_37))))), inference(resolution, [status(thm)], [c_6, c_131])).
% 3.67/1.73  tff(c_494, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, B_61) | ~r1_xboole_0(A_60, C_62) | ~r1_tarski(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.67/1.73  tff(c_555, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~r1_xboole_0(A_36, k4_xboole_0(A_36, B_37)))), inference(resolution, [status(thm)], [c_150, c_494])).
% 3.67/1.73  tff(c_1779, plain, (![B_106]: (r1_tarski('#skF_1', B_106) | k10_relat_1('#skF_3', k4_xboole_0('#skF_1', B_106))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1765, c_555])).
% 3.67/1.73  tff(c_1801, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_842, c_1779])).
% 3.67/1.73  tff(c_1851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1801])).
% 3.67/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.73  
% 3.67/1.73  Inference rules
% 3.67/1.73  ----------------------
% 3.67/1.73  #Ref     : 0
% 3.67/1.73  #Sup     : 472
% 3.67/1.73  #Fact    : 0
% 3.67/1.73  #Define  : 0
% 3.67/1.73  #Split   : 3
% 3.67/1.73  #Chain   : 0
% 3.67/1.73  #Close   : 0
% 3.67/1.73  
% 3.67/1.73  Ordering : KBO
% 3.67/1.73  
% 3.67/1.73  Simplification rules
% 3.67/1.73  ----------------------
% 3.67/1.73  #Subsume      : 17
% 3.67/1.73  #Demod        : 161
% 3.67/1.73  #Tautology    : 160
% 3.67/1.73  #SimpNegUnit  : 1
% 3.67/1.73  #BackRed      : 0
% 3.67/1.73  
% 3.67/1.73  #Partial instantiations: 0
% 3.67/1.73  #Strategies tried      : 1
% 3.67/1.73  
% 3.67/1.73  Timing (in seconds)
% 3.67/1.73  ----------------------
% 3.67/1.73  Preprocessing        : 0.38
% 3.67/1.73  Parsing              : 0.22
% 3.67/1.73  CNF conversion       : 0.02
% 3.67/1.73  Main loop            : 0.57
% 3.67/1.73  Inferencing          : 0.19
% 3.67/1.73  Reduction            : 0.20
% 3.67/1.73  Demodulation         : 0.15
% 3.67/1.73  BG Simplification    : 0.03
% 3.67/1.73  Subsumption          : 0.12
% 3.67/1.73  Abstraction          : 0.03
% 3.67/1.73  MUC search           : 0.00
% 3.67/1.73  Cooper               : 0.00
% 3.67/1.73  Total                : 0.98
% 3.67/1.73  Index Insertion      : 0.00
% 3.67/1.73  Index Deletion       : 0.00
% 3.67/1.73  Index Matching       : 0.00
% 3.67/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
