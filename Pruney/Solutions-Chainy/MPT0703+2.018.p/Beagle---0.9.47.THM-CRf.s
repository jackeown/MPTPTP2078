%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   58 (  99 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 195 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_137,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_145,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_24])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_18,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( k6_subset_1(k10_relat_1(C_15,A_13),k10_relat_1(C_15,B_14)) = k10_relat_1(C_15,k6_subset_1(A_13,B_14))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_532,plain,(
    ! [C_55,A_56,B_57] :
      ( k4_xboole_0(k10_relat_1(C_55,A_56),k10_relat_1(C_55,B_57)) = k10_relat_1(C_55,k4_xboole_0(A_56,B_57))
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_20])).

tff(c_551,plain,(
    ! [C_55,B_57] :
      ( k10_relat_1(C_55,k4_xboole_0(B_57,B_57)) = k1_xboole_0
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_62])).

tff(c_588,plain,(
    ! [C_58] :
      ( k10_relat_1(C_58,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_551])).

tff(c_591,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_588])).

tff(c_594,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_591])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_228,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_293,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_43,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k9_relat_1(B_17,k10_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k2_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_295,plain,(
    ! [A_43] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_43)) = A_43
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_43,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_293,c_22])).

tff(c_915,plain,(
    ! [A_73] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_73)) = A_73
      | ~ r1_tarski(A_73,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_295])).

tff(c_930,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_915])).

tff(c_945,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_930])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_10])).

tff(c_544,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_67])).

tff(c_567,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_544])).

tff(c_933,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_915])).

tff(c_947,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_933])).

tff(c_956,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_947])).

tff(c_957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:39:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.41  
% 2.74/1.41  %Foreground sorts:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Background operators:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Foreground operators:
% 2.74/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.74/1.41  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.74/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.74/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.41  
% 2.74/1.43  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.74/1.43  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 2.74/1.43  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.74/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/1.43  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.74/1.43  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 2.74/1.43  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.74/1.43  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.74/1.43  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.74/1.43  tff(c_137, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.43  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.43  tff(c_145, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_24])).
% 2.74/1.43  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.74/1.43  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.43  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.43  tff(c_47, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.43  tff(c_62, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_47])).
% 2.74/1.43  tff(c_18, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.43  tff(c_20, plain, (![C_15, A_13, B_14]: (k6_subset_1(k10_relat_1(C_15, A_13), k10_relat_1(C_15, B_14))=k10_relat_1(C_15, k6_subset_1(A_13, B_14)) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.43  tff(c_532, plain, (![C_55, A_56, B_57]: (k4_xboole_0(k10_relat_1(C_55, A_56), k10_relat_1(C_55, B_57))=k10_relat_1(C_55, k4_xboole_0(A_56, B_57)) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_20])).
% 2.74/1.43  tff(c_551, plain, (![C_55, B_57]: (k10_relat_1(C_55, k4_xboole_0(B_57, B_57))=k1_xboole_0 | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_532, c_62])).
% 2.74/1.43  tff(c_588, plain, (![C_58]: (k10_relat_1(C_58, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_551])).
% 2.74/1.43  tff(c_591, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_588])).
% 2.74/1.43  tff(c_594, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_591])).
% 2.74/1.43  tff(c_26, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.43  tff(c_228, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.43  tff(c_293, plain, (![A_43]: (r1_tarski(A_43, k2_relat_1('#skF_3')) | ~r1_tarski(A_43, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_228])).
% 2.74/1.43  tff(c_22, plain, (![B_17, A_16]: (k9_relat_1(B_17, k10_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k2_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.43  tff(c_295, plain, (![A_43]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_43))=A_43 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_43, '#skF_1'))), inference(resolution, [status(thm)], [c_293, c_22])).
% 2.74/1.43  tff(c_915, plain, (![A_73]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_73))=A_73 | ~r1_tarski(A_73, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_295])).
% 2.74/1.43  tff(c_930, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_594, c_915])).
% 2.74/1.43  tff(c_945, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_930])).
% 2.74/1.43  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.43  tff(c_28, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.74/1.43  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.43  tff(c_67, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_10])).
% 2.74/1.43  tff(c_544, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_532, c_67])).
% 2.74/1.43  tff(c_567, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_544])).
% 2.74/1.43  tff(c_933, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_567, c_915])).
% 2.74/1.43  tff(c_947, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_933])).
% 2.74/1.43  tff(c_956, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_945, c_947])).
% 2.74/1.43  tff(c_957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_956])).
% 2.74/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  Inference rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Ref     : 0
% 2.74/1.43  #Sup     : 217
% 2.74/1.43  #Fact    : 0
% 2.74/1.43  #Define  : 0
% 2.74/1.43  #Split   : 2
% 2.74/1.43  #Chain   : 0
% 2.74/1.43  #Close   : 0
% 2.74/1.43  
% 2.74/1.43  Ordering : KBO
% 2.74/1.43  
% 2.74/1.43  Simplification rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Subsume      : 27
% 2.74/1.43  #Demod        : 144
% 2.74/1.43  #Tautology    : 118
% 2.74/1.43  #SimpNegUnit  : 1
% 2.74/1.43  #BackRed      : 0
% 2.74/1.43  
% 2.74/1.43  #Partial instantiations: 0
% 2.74/1.43  #Strategies tried      : 1
% 2.74/1.43  
% 2.74/1.43  Timing (in seconds)
% 2.74/1.43  ----------------------
% 2.74/1.43  Preprocessing        : 0.31
% 2.74/1.43  Parsing              : 0.17
% 2.74/1.43  CNF conversion       : 0.02
% 2.74/1.43  Main loop            : 0.34
% 2.74/1.43  Inferencing          : 0.12
% 2.74/1.43  Reduction            : 0.11
% 2.74/1.43  Demodulation         : 0.08
% 2.74/1.43  BG Simplification    : 0.02
% 2.74/1.43  Subsumption          : 0.07
% 2.74/1.43  Abstraction          : 0.02
% 2.74/1.43  MUC search           : 0.00
% 2.74/1.43  Cooper               : 0.00
% 2.74/1.43  Total                : 0.69
% 2.74/1.43  Index Insertion      : 0.00
% 2.74/1.43  Index Deletion       : 0.00
% 2.74/1.43  Index Matching       : 0.00
% 2.74/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
