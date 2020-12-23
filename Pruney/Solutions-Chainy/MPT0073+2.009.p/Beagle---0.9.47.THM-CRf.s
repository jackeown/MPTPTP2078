%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:25 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 136 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 219 expanded)
%              Number of equality atoms :   37 ( 137 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_16,plain,
    ( k1_xboole_0 != '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_195,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_245,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_230])).

tff(c_248,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_245])).

tff(c_14,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_34,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_22])).

tff(c_33,plain,(
    ! [A_5] : k4_xboole_0(A_5,'#skF_2') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_35,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = '#skF_2'
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_89,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_35,c_73])).

tff(c_90,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_90])).

tff(c_135,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_105])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [A_24] : k4_xboole_0(A_24,'#skF_2') = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_10])).

tff(c_152,plain,(
    ! [A_24] : k3_xboole_0(A_24,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_140])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_18])).

tff(c_88,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_53,c_73])).

tff(c_156,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_88])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_156])).

tff(c_159,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_194,plain,(
    k3_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_159,c_179])).

tff(c_270,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,k4_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_230])).

tff(c_288,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_1')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_270])).

tff(c_293,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_248,c_8,c_288])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_293])).

tff(c_297,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_296,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_303,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_296])).

tff(c_298,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_12])).

tff(c_313,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_298])).

tff(c_20,plain,
    ( k1_xboole_0 != '#skF_1'
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_303,c_303,c_297,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.28  
% 1.89/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.28  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.89/1.28  
% 1.89/1.28  %Foreground sorts:
% 1.89/1.28  
% 1.89/1.28  
% 1.89/1.28  %Background operators:
% 1.89/1.28  
% 1.89/1.28  
% 1.89/1.28  %Foreground operators:
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.28  
% 1.89/1.29  tff(f_52, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.89/1.29  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.89/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.89/1.29  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.89/1.29  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.89/1.29  tff(c_16, plain, (k1_xboole_0!='#skF_1' | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.29  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_16])).
% 1.89/1.29  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.29  tff(c_179, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.29  tff(c_195, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_179])).
% 1.89/1.29  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.29  tff(c_230, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.29  tff(c_245, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_230])).
% 1.89/1.29  tff(c_248, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_245])).
% 1.89/1.29  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_1') | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.29  tff(c_32, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_14])).
% 1.89/1.29  tff(c_34, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_22])).
% 1.89/1.29  tff(c_33, plain, (![A_5]: (k4_xboole_0(A_5, '#skF_2')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 1.89/1.29  tff(c_35, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 1.89/1.29  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.29  tff(c_73, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)='#skF_2' | ~r1_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2])).
% 1.89/1.29  tff(c_89, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_35, c_73])).
% 1.89/1.29  tff(c_90, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.29  tff(c_105, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_90])).
% 1.89/1.29  tff(c_135, plain, (![A_24]: (k4_xboole_0(A_24, A_24)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_105])).
% 1.89/1.29  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.29  tff(c_140, plain, (![A_24]: (k4_xboole_0(A_24, '#skF_2')=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_135, c_10])).
% 1.89/1.29  tff(c_152, plain, (![A_24]: (k3_xboole_0(A_24, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_33, c_140])).
% 1.89/1.29  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_1') | ~r1_xboole_0('#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.29  tff(c_53, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_18])).
% 1.89/1.29  tff(c_88, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_53, c_73])).
% 1.89/1.29  tff(c_156, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_88])).
% 1.89/1.29  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_156])).
% 1.89/1.29  tff(c_159, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_14])).
% 1.89/1.29  tff(c_194, plain, (k3_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_159, c_179])).
% 1.89/1.29  tff(c_270, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k3_xboole_0(A_39, k4_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_230])).
% 1.89/1.29  tff(c_288, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_1'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_194, c_270])).
% 1.89/1.29  tff(c_293, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_248, c_8, c_288])).
% 1.89/1.29  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_293])).
% 1.89/1.29  tff(c_297, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 1.89/1.29  tff(c_296, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16])).
% 1.89/1.29  tff(c_303, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_297, c_296])).
% 1.89/1.29  tff(c_298, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_12])).
% 1.89/1.29  tff(c_313, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_298])).
% 1.89/1.29  tff(c_20, plain, (k1_xboole_0!='#skF_1' | ~r1_xboole_0('#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.29  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_313, c_303, c_303, c_297, c_20])).
% 1.89/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.29  
% 1.89/1.29  Inference rules
% 1.89/1.29  ----------------------
% 1.89/1.29  #Ref     : 0
% 1.89/1.29  #Sup     : 74
% 1.89/1.29  #Fact    : 0
% 1.89/1.29  #Define  : 0
% 1.89/1.29  #Split   : 2
% 1.89/1.29  #Chain   : 0
% 1.89/1.29  #Close   : 0
% 1.89/1.29  
% 1.89/1.29  Ordering : KBO
% 1.89/1.29  
% 1.89/1.29  Simplification rules
% 1.89/1.29  ----------------------
% 1.89/1.29  #Subsume      : 3
% 1.89/1.29  #Demod        : 35
% 1.89/1.29  #Tautology    : 53
% 1.89/1.29  #SimpNegUnit  : 2
% 1.89/1.29  #BackRed      : 6
% 1.89/1.29  
% 1.89/1.29  #Partial instantiations: 0
% 1.89/1.29  #Strategies tried      : 1
% 1.89/1.29  
% 1.89/1.29  Timing (in seconds)
% 1.89/1.29  ----------------------
% 1.89/1.30  Preprocessing        : 0.29
% 1.89/1.30  Parsing              : 0.16
% 1.89/1.30  CNF conversion       : 0.02
% 1.89/1.30  Main loop            : 0.18
% 1.89/1.30  Inferencing          : 0.07
% 1.89/1.30  Reduction            : 0.06
% 1.89/1.30  Demodulation         : 0.04
% 1.89/1.30  BG Simplification    : 0.01
% 1.89/1.30  Subsumption          : 0.03
% 1.89/1.30  Abstraction          : 0.01
% 1.89/1.30  MUC search           : 0.00
% 1.89/1.30  Cooper               : 0.00
% 1.89/1.30  Total                : 0.50
% 1.89/1.30  Index Insertion      : 0.00
% 1.89/1.30  Index Deletion       : 0.00
% 1.89/1.30  Index Matching       : 0.00
% 1.89/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
