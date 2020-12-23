%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:44 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 207 expanded)
%              Number of leaves         :   21 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :   76 ( 407 expanded)
%              Number of equality atoms :   23 ( 105 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    ! [B_26,A_27] :
      ( k1_relat_1(k7_relat_1(B_26,A_27)) = A_27
      | ~ r1_tarski(A_27,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_109,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k1_relat_1(k7_relat_1(B_11,A_10)) = A_10
      | ~ r1_tarski(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12])).

tff(c_207,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_210,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_210])).

tff(c_216,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_10,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [A_28,C_29,B_30] :
      ( k3_xboole_0(A_28,k10_relat_1(C_29,B_30)) = k10_relat_1(k7_relat_1(C_29,A_28),B_30)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_149,plain,(
    ! [C_31,A_32,B_33] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_31,A_32),B_33),A_32)
      | ~ v1_relat_1(C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_4])).

tff(c_2028,plain,(
    ! [B_99,C_100,B_101] :
      ( k1_relat_1(k7_relat_1(B_99,k10_relat_1(k7_relat_1(C_100,k1_relat_1(B_99)),B_101))) = k10_relat_1(k7_relat_1(C_100,k1_relat_1(B_99)),B_101)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(C_100) ) ),
    inference(resolution,[status(thm)],[c_149,c_12])).

tff(c_2136,plain,(
    ! [C_100,B_101] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(k7_relat_1(C_100,'#skF_1'),B_101))) = k10_relat_1(k7_relat_1(C_100,k1_relat_1(k7_relat_1('#skF_2','#skF_1'))),B_101)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(C_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2028])).

tff(c_2194,plain,(
    ! [C_104,B_105] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k10_relat_1(k7_relat_1(C_104,'#skF_1'),B_105))) = k10_relat_1(k7_relat_1(C_104,'#skF_1'),B_105)
      | ~ v1_relat_1(C_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_109,c_2136])).

tff(c_3248,plain,(
    ! [C_132] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),k1_relat_1(k7_relat_1(C_132,'#skF_1')))) = k10_relat_1(k7_relat_1(C_132,'#skF_1'),k2_relat_1(k7_relat_1(C_132,'#skF_1')))
      | ~ v1_relat_1(C_132)
      | ~ v1_relat_1(k7_relat_1(C_132,'#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2194])).

tff(c_3371,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_3248])).

tff(c_3386,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_20,c_3371])).

tff(c_3451,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3386,c_10])).

tff(c_3499,plain,(
    k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_109,c_3451])).

tff(c_3505,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3386])).

tff(c_23,plain,(
    ! [B_19,A_20] : k3_xboole_0(B_19,A_20) = k3_xboole_0(A_20,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [B_19,A_20] : r1_tarski(k3_xboole_0(B_19,A_20),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_4])).

tff(c_123,plain,(
    ! [C_29,A_28,B_30] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_29,A_28),B_30),k10_relat_1(C_29,B_30))
      | ~ v1_relat_1(C_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_38])).

tff(c_3652,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3505,c_123])).

tff(c_3704,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3652])).

tff(c_3720,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3704])).

tff(c_3722,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3720])).

tff(c_3724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_3722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.95  
% 4.68/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.95  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.01/1.95  
% 5.01/1.95  %Foreground sorts:
% 5.01/1.95  
% 5.01/1.95  
% 5.01/1.95  %Background operators:
% 5.01/1.95  
% 5.01/1.95  
% 5.01/1.95  %Foreground operators:
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.01/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.01/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.01/1.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.01/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.95  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.01/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.01/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.01/1.95  
% 5.01/1.97  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.01/1.97  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.01/1.97  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.01/1.97  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 5.01/1.97  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.01/1.97  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.01/1.97  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.01/1.97  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.01/1.97  tff(c_16, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.01/1.97  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.01/1.97  tff(c_8, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.01/1.97  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.01/1.97  tff(c_18, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.01/1.97  tff(c_93, plain, (![B_26, A_27]: (k1_relat_1(k7_relat_1(B_26, A_27))=A_27 | ~r1_tarski(A_27, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.01/1.97  tff(c_104, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_93])).
% 5.01/1.97  tff(c_109, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_104])).
% 5.01/1.97  tff(c_12, plain, (![B_11, A_10]: (k1_relat_1(k7_relat_1(B_11, A_10))=A_10 | ~r1_tarski(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.01/1.97  tff(c_113, plain, (![A_10]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_109, c_12])).
% 5.01/1.97  tff(c_207, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_113])).
% 5.01/1.97  tff(c_210, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_207])).
% 5.01/1.97  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_210])).
% 5.01/1.97  tff(c_216, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_113])).
% 5.01/1.97  tff(c_10, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/1.97  tff(c_117, plain, (![A_28, C_29, B_30]: (k3_xboole_0(A_28, k10_relat_1(C_29, B_30))=k10_relat_1(k7_relat_1(C_29, A_28), B_30) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.01/1.97  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.01/1.97  tff(c_149, plain, (![C_31, A_32, B_33]: (r1_tarski(k10_relat_1(k7_relat_1(C_31, A_32), B_33), A_32) | ~v1_relat_1(C_31))), inference(superposition, [status(thm), theory('equality')], [c_117, c_4])).
% 5.01/1.97  tff(c_2028, plain, (![B_99, C_100, B_101]: (k1_relat_1(k7_relat_1(B_99, k10_relat_1(k7_relat_1(C_100, k1_relat_1(B_99)), B_101)))=k10_relat_1(k7_relat_1(C_100, k1_relat_1(B_99)), B_101) | ~v1_relat_1(B_99) | ~v1_relat_1(C_100))), inference(resolution, [status(thm)], [c_149, c_12])).
% 5.01/1.97  tff(c_2136, plain, (![C_100, B_101]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(k7_relat_1(C_100, '#skF_1'), B_101)))=k10_relat_1(k7_relat_1(C_100, k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), B_101) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(C_100))), inference(superposition, [status(thm), theory('equality')], [c_109, c_2028])).
% 5.01/1.97  tff(c_2194, plain, (![C_104, B_105]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k10_relat_1(k7_relat_1(C_104, '#skF_1'), B_105)))=k10_relat_1(k7_relat_1(C_104, '#skF_1'), B_105) | ~v1_relat_1(C_104))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_109, c_2136])).
% 5.01/1.97  tff(c_3248, plain, (![C_132]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), k1_relat_1(k7_relat_1(C_132, '#skF_1'))))=k10_relat_1(k7_relat_1(C_132, '#skF_1'), k2_relat_1(k7_relat_1(C_132, '#skF_1'))) | ~v1_relat_1(C_132) | ~v1_relat_1(k7_relat_1(C_132, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2194])).
% 5.01/1.97  tff(c_3371, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_3248])).
% 5.01/1.97  tff(c_3386, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_20, c_3371])).
% 5.01/1.97  tff(c_3451, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3386, c_10])).
% 5.01/1.97  tff(c_3499, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_109, c_3451])).
% 5.01/1.97  tff(c_3505, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3386])).
% 5.01/1.97  tff(c_23, plain, (![B_19, A_20]: (k3_xboole_0(B_19, A_20)=k3_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.01/1.97  tff(c_38, plain, (![B_19, A_20]: (r1_tarski(k3_xboole_0(B_19, A_20), A_20))), inference(superposition, [status(thm), theory('equality')], [c_23, c_4])).
% 5.01/1.97  tff(c_123, plain, (![C_29, A_28, B_30]: (r1_tarski(k10_relat_1(k7_relat_1(C_29, A_28), B_30), k10_relat_1(C_29, B_30)) | ~v1_relat_1(C_29))), inference(superposition, [status(thm), theory('equality')], [c_117, c_38])).
% 5.01/1.97  tff(c_3652, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3505, c_123])).
% 5.01/1.97  tff(c_3704, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3652])).
% 5.01/1.97  tff(c_3720, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_3704])).
% 5.01/1.97  tff(c_3722, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3720])).
% 5.01/1.97  tff(c_3724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_3722])).
% 5.01/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.97  
% 5.01/1.97  Inference rules
% 5.01/1.97  ----------------------
% 5.01/1.97  #Ref     : 0
% 5.01/1.97  #Sup     : 898
% 5.01/1.97  #Fact    : 0
% 5.01/1.97  #Define  : 0
% 5.01/1.97  #Split   : 2
% 5.01/1.97  #Chain   : 0
% 5.01/1.97  #Close   : 0
% 5.01/1.97  
% 5.01/1.97  Ordering : KBO
% 5.01/1.97  
% 5.01/1.97  Simplification rules
% 5.01/1.97  ----------------------
% 5.01/1.97  #Subsume      : 106
% 5.01/1.97  #Demod        : 604
% 5.01/1.97  #Tautology    : 242
% 5.01/1.97  #SimpNegUnit  : 1
% 5.01/1.97  #BackRed      : 8
% 5.01/1.97  
% 5.01/1.97  #Partial instantiations: 0
% 5.01/1.97  #Strategies tried      : 1
% 5.01/1.97  
% 5.01/1.97  Timing (in seconds)
% 5.01/1.97  ----------------------
% 5.01/1.97  Preprocessing        : 0.29
% 5.01/1.97  Parsing              : 0.16
% 5.01/1.97  CNF conversion       : 0.02
% 5.01/1.97  Main loop            : 0.89
% 5.01/1.97  Inferencing          : 0.30
% 5.01/1.97  Reduction            : 0.36
% 5.01/1.97  Demodulation         : 0.29
% 5.01/1.97  BG Simplification    : 0.04
% 5.01/1.97  Subsumption          : 0.15
% 5.01/1.97  Abstraction          : 0.05
% 5.01/1.97  MUC search           : 0.00
% 5.01/1.97  Cooper               : 0.00
% 5.01/1.97  Total                : 1.21
% 5.01/1.97  Index Insertion      : 0.00
% 5.01/1.97  Index Deletion       : 0.00
% 5.01/1.97  Index Matching       : 0.00
% 5.01/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
