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
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   52 (  91 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 182 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => ( r1_tarski(C,B)
           => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t210_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_17] :
      ( k7_relat_1(A_17,k1_relat_1(A_17)) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [B_20,A_21] :
      ( r1_tarski(k7_relat_1(B_20,A_21),B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    ! [A_27] :
      ( r1_tarski(A_27,A_27)
      | ~ v1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_40])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_28] :
      ( k2_xboole_0(A_28,A_28) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_66,plain,(
    k2_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_248,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,k2_xboole_0(A_46,B_47))
      | ~ v1_relat_1(k2_xboole_0(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_269,plain,
    ( r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1(k2_xboole_0('#skF_1','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_248])).

tff(c_281,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66,c_269])).

tff(c_373,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_relat_1(A_61),k1_relat_1(B_62))
      | ~ r1_tarski(A_61,B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( v4_relat_1(B_7,A_6)
      | ~ r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_380,plain,(
    ! [A_61,B_62] :
      ( v4_relat_1(A_61,k1_relat_1(B_62))
      | ~ r1_tarski(A_61,B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_373,c_6])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_74,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_103,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_30])).

tff(c_107,plain,(
    k2_xboole_0('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) = k7_relat_1('#skF_2',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_167,plain,(
    ! [C_38] :
      ( r1_tarski('#skF_1',C_38)
      | ~ r1_tarski(k7_relat_1('#skF_2',k1_relat_1('#skF_1')),C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_2])).

tff(c_179,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_167])).

tff(c_185,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_179])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_185])).

tff(c_189,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_429,plain,(
    ! [C_69,B_70,A_71] :
      ( r1_tarski(C_69,k7_relat_1(B_70,A_71))
      | ~ r1_tarski(C_69,B_70)
      | ~ v4_relat_1(C_69,A_71)
      | ~ v1_relat_1(C_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_188,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_442,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v4_relat_1('#skF_1',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_429,c_188])).

tff(c_460,plain,(
    ~ v4_relat_1('#skF_1',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_189,c_442])).

tff(c_465,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_380,c_460])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_281,c_465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.37  
% 2.31/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.37  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.31/1.37  
% 2.31/1.37  %Foreground sorts:
% 2.31/1.37  
% 2.31/1.37  
% 2.31/1.37  %Background operators:
% 2.31/1.37  
% 2.31/1.37  
% 2.31/1.37  %Foreground operators:
% 2.31/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.31/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.37  
% 2.31/1.39  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t219_relat_1)).
% 2.31/1.39  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.31/1.39  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.31/1.39  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.31/1.39  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.31/1.39  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.31/1.39  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.31/1.39  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => (r1_tarski(C, B) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t210_relat_1)).
% 2.31/1.39  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.39  tff(c_18, plain, (![A_17]: (k7_relat_1(A_17, k1_relat_1(A_17))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.39  tff(c_40, plain, (![B_20, A_21]: (r1_tarski(k7_relat_1(B_20, A_21), B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.39  tff(c_50, plain, (![A_27]: (r1_tarski(A_27, A_27) | ~v1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_18, c_40])).
% 2.31/1.39  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.39  tff(c_60, plain, (![A_28]: (k2_xboole_0(A_28, A_28)=A_28 | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_50, c_4])).
% 2.31/1.39  tff(c_66, plain, (k2_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_60])).
% 2.31/1.39  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.39  tff(c_248, plain, (![A_46, B_47]: (r1_tarski(A_46, k2_xboole_0(A_46, B_47)) | ~v1_relat_1(k2_xboole_0(A_46, B_47)))), inference(resolution, [status(thm)], [c_50, c_2])).
% 2.31/1.39  tff(c_269, plain, (r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1(k2_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_248])).
% 2.31/1.39  tff(c_281, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_66, c_269])).
% 2.31/1.39  tff(c_373, plain, (![A_61, B_62]: (r1_tarski(k1_relat_1(A_61), k1_relat_1(B_62)) | ~r1_tarski(A_61, B_62) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.39  tff(c_6, plain, (![B_7, A_6]: (v4_relat_1(B_7, A_6) | ~r1_tarski(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.39  tff(c_380, plain, (![A_61, B_62]: (v4_relat_1(A_61, k1_relat_1(B_62)) | ~r1_tarski(A_61, B_62) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_373, c_6])).
% 2.31/1.39  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.39  tff(c_24, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.39  tff(c_74, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 2.31/1.39  tff(c_16, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.39  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.39  tff(c_103, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_74, c_30])).
% 2.31/1.39  tff(c_107, plain, (k2_xboole_0('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))=k7_relat_1('#skF_2', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_103, c_4])).
% 2.31/1.39  tff(c_167, plain, (![C_38]: (r1_tarski('#skF_1', C_38) | ~r1_tarski(k7_relat_1('#skF_2', k1_relat_1('#skF_1')), C_38))), inference(superposition, [status(thm), theory('equality')], [c_107, c_2])).
% 2.31/1.39  tff(c_179, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_167])).
% 2.31/1.39  tff(c_185, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_179])).
% 2.31/1.39  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_185])).
% 2.31/1.39  tff(c_189, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 2.31/1.39  tff(c_429, plain, (![C_69, B_70, A_71]: (r1_tarski(C_69, k7_relat_1(B_70, A_71)) | ~r1_tarski(C_69, B_70) | ~v4_relat_1(C_69, A_71) | ~v1_relat_1(C_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.31/1.39  tff(c_188, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_24])).
% 2.31/1.39  tff(c_442, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v4_relat_1('#skF_1', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_429, c_188])).
% 2.31/1.39  tff(c_460, plain, (~v4_relat_1('#skF_1', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_189, c_442])).
% 2.31/1.39  tff(c_465, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_380, c_460])).
% 2.31/1.39  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_281, c_465])).
% 2.31/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.39  
% 2.31/1.39  Inference rules
% 2.31/1.39  ----------------------
% 2.31/1.39  #Ref     : 0
% 2.31/1.39  #Sup     : 105
% 2.31/1.39  #Fact    : 0
% 2.31/1.39  #Define  : 0
% 2.31/1.39  #Split   : 1
% 2.31/1.39  #Chain   : 0
% 2.31/1.39  #Close   : 0
% 2.31/1.39  
% 2.31/1.39  Ordering : KBO
% 2.31/1.39  
% 2.31/1.39  Simplification rules
% 2.31/1.39  ----------------------
% 2.31/1.39  #Subsume      : 10
% 2.31/1.39  #Demod        : 36
% 2.31/1.39  #Tautology    : 43
% 2.31/1.39  #SimpNegUnit  : 3
% 2.31/1.39  #BackRed      : 0
% 2.31/1.39  
% 2.31/1.39  #Partial instantiations: 0
% 2.31/1.39  #Strategies tried      : 1
% 2.31/1.39  
% 2.31/1.39  Timing (in seconds)
% 2.31/1.39  ----------------------
% 2.54/1.39  Preprocessing        : 0.27
% 2.54/1.39  Parsing              : 0.15
% 2.54/1.39  CNF conversion       : 0.02
% 2.54/1.39  Main loop            : 0.28
% 2.54/1.39  Inferencing          : 0.12
% 2.54/1.39  Reduction            : 0.07
% 2.54/1.39  Demodulation         : 0.05
% 2.54/1.39  BG Simplification    : 0.01
% 2.54/1.39  Subsumption          : 0.06
% 2.54/1.39  Abstraction          : 0.01
% 2.54/1.39  MUC search           : 0.00
% 2.54/1.39  Cooper               : 0.00
% 2.54/1.39  Total                : 0.58
% 2.54/1.39  Index Insertion      : 0.00
% 2.54/1.39  Index Deletion       : 0.00
% 2.54/1.39  Index Matching       : 0.00
% 2.54/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
