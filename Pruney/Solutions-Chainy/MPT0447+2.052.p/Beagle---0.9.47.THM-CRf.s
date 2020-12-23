%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:34 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   46 (  76 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 160 expanded)
%              Number of equality atoms :    3 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k2_relat_1(A_13),k2_relat_1(B_15))
      | ~ r1_tarski(A_13,B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_25,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_1,A_22] :
      ( r1_tarski(A_1,k3_relat_1(A_22))
      | ~ r1_tarski(A_1,k2_relat_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_2])).

tff(c_14,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k1_relat_1(A_13),k1_relat_1(B_15))
      | ~ r1_tarski(A_13,B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_12] :
      ( k2_xboole_0(k1_relat_1(A_12),k2_relat_1(A_12)) = k3_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_tarski(A_24,C_25)
      | ~ r1_tarski(B_26,C_25)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_28,A_29,B_30] :
      ( r1_tarski(A_28,k2_xboole_0(A_29,B_30))
      | ~ r1_tarski(A_28,A_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_63,plain,(
    ! [A_28,A_12] :
      ( r1_tarski(A_28,k3_relat_1(A_12))
      | ~ r1_tarski(A_28,k1_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_102,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(k2_xboole_0(A_37,C_38),B_39)
      | ~ r1_tarski(C_38,B_39)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_723,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(k3_relat_1(A_135),B_136)
      | ~ r1_tarski(k2_relat_1(A_135),B_136)
      | ~ r1_tarski(k1_relat_1(A_135),B_136)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_16,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_747,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_723,c_16])).

tff(c_762,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_747])).

tff(c_763,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_762])).

tff(c_766,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_763])).

tff(c_772,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_766])).

tff(c_778,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_772])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_778])).

tff(c_783,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_855,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_783])).

tff(c_861,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_855])).

tff(c_879,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_861])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.83/1.43  
% 2.83/1.43  %Foreground sorts:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Background operators:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Foreground operators:
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.43  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.83/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.43  
% 2.83/1.44  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.83/1.44  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.83/1.44  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.83/1.44  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.83/1.44  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.83/1.44  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.83/1.44  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.83/1.44  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.44  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.44  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.44  tff(c_12, plain, (![A_13, B_15]: (r1_tarski(k2_relat_1(A_13), k2_relat_1(B_15)) | ~r1_tarski(A_13, B_15) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.44  tff(c_25, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.44  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.44  tff(c_31, plain, (![A_1, A_22]: (r1_tarski(A_1, k3_relat_1(A_22)) | ~r1_tarski(A_1, k2_relat_1(A_22)) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_25, c_2])).
% 2.83/1.44  tff(c_14, plain, (![A_13, B_15]: (r1_tarski(k1_relat_1(A_13), k1_relat_1(B_15)) | ~r1_tarski(A_13, B_15) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.44  tff(c_10, plain, (![A_12]: (k2_xboole_0(k1_relat_1(A_12), k2_relat_1(A_12))=k3_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.44  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.44  tff(c_41, plain, (![A_24, C_25, B_26]: (r1_tarski(A_24, C_25) | ~r1_tarski(B_26, C_25) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.83/1.44  tff(c_58, plain, (![A_28, A_29, B_30]: (r1_tarski(A_28, k2_xboole_0(A_29, B_30)) | ~r1_tarski(A_28, A_29))), inference(resolution, [status(thm)], [c_6, c_41])).
% 2.83/1.44  tff(c_63, plain, (![A_28, A_12]: (r1_tarski(A_28, k3_relat_1(A_12)) | ~r1_tarski(A_28, k1_relat_1(A_12)) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 2.83/1.44  tff(c_102, plain, (![A_37, C_38, B_39]: (r1_tarski(k2_xboole_0(A_37, C_38), B_39) | ~r1_tarski(C_38, B_39) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.44  tff(c_723, plain, (![A_135, B_136]: (r1_tarski(k3_relat_1(A_135), B_136) | ~r1_tarski(k2_relat_1(A_135), B_136) | ~r1_tarski(k1_relat_1(A_135), B_136) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 2.83/1.44  tff(c_16, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.44  tff(c_747, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_723, c_16])).
% 2.83/1.44  tff(c_762, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_747])).
% 2.83/1.44  tff(c_763, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_762])).
% 2.83/1.44  tff(c_766, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_63, c_763])).
% 2.83/1.44  tff(c_772, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_766])).
% 2.83/1.44  tff(c_778, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_772])).
% 2.83/1.44  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_778])).
% 2.83/1.44  tff(c_783, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_762])).
% 2.83/1.44  tff(c_855, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_31, c_783])).
% 2.83/1.44  tff(c_861, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_855])).
% 2.83/1.44  tff(c_879, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_861])).
% 2.83/1.44  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_879])).
% 2.83/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  Inference rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Ref     : 0
% 2.83/1.44  #Sup     : 242
% 2.83/1.44  #Fact    : 0
% 2.83/1.44  #Define  : 0
% 2.83/1.44  #Split   : 2
% 2.83/1.44  #Chain   : 0
% 2.83/1.44  #Close   : 0
% 2.83/1.44  
% 2.83/1.44  Ordering : KBO
% 2.83/1.44  
% 2.83/1.44  Simplification rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Subsume      : 37
% 2.83/1.44  #Demod        : 20
% 2.83/1.44  #Tautology    : 7
% 2.83/1.44  #SimpNegUnit  : 0
% 2.83/1.44  #BackRed      : 0
% 2.83/1.44  
% 2.83/1.44  #Partial instantiations: 0
% 2.83/1.44  #Strategies tried      : 1
% 2.83/1.44  
% 2.83/1.44  Timing (in seconds)
% 2.83/1.44  ----------------------
% 2.83/1.44  Preprocessing        : 0.26
% 2.83/1.44  Parsing              : 0.15
% 2.83/1.44  CNF conversion       : 0.02
% 2.83/1.44  Main loop            : 0.43
% 2.83/1.44  Inferencing          : 0.15
% 2.83/1.44  Reduction            : 0.11
% 2.83/1.44  Demodulation         : 0.08
% 2.83/1.44  BG Simplification    : 0.02
% 2.83/1.44  Subsumption          : 0.12
% 2.83/1.45  Abstraction          : 0.02
% 2.83/1.45  MUC search           : 0.00
% 2.83/1.45  Cooper               : 0.00
% 2.83/1.45  Total                : 0.72
% 2.83/1.45  Index Insertion      : 0.00
% 2.83/1.45  Index Deletion       : 0.00
% 2.83/1.45  Index Matching       : 0.00
% 2.83/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
