%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 124 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :    6
%              Number of atoms          :   72 ( 224 expanded)
%              Number of equality atoms :   39 ( 133 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_29,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_14,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_24,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_tarski(B_4) = A_3
      | k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_tarski(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_55,c_8])).

tff(c_64,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_30,c_58])).

tff(c_65,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_67,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_68,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_31])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_72,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,k1_tarski(B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [B_4] : r1_tarski('#skF_1',k1_tarski(B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_31])).

tff(c_85,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_108,plain,(
    ! [B_15,A_16] :
      ( k1_tarski(B_15) = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_85,c_108])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_30,c_114])).

tff(c_128,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_16,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_16])).

tff(c_138,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_141,plain,(
    ! [B_4] : r1_tarski('#skF_1',k1_tarski(B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_127])).

tff(c_150,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_152,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_127])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_152])).

tff(c_157,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_157,c_20])).

tff(c_166,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_158,plain,(
    ! [B_4] : r1_tarski('#skF_3',k1_tarski(B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_12])).

tff(c_169,plain,(
    ! [B_4] : r1_tarski('#skF_1',k1_tarski(B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_158])).

tff(c_156,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_156])).

tff(c_183,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_185,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_156])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:50:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.17  
% 1.79/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.17  %$ r1_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.79/1.17  
% 1.79/1.17  %Foreground sorts:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Background operators:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Foreground operators:
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.17  
% 1.79/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.79/1.18  tff(f_44, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 1.79/1.18  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.79/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.18  tff(c_18, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.18  tff(c_29, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 1.79/1.18  tff(c_14, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.18  tff(c_30, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 1.79/1.18  tff(c_24, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.18  tff(c_55, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_24])).
% 1.79/1.18  tff(c_8, plain, (![B_4, A_3]: (k1_tarski(B_4)=A_3 | k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_tarski(B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.18  tff(c_58, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_55, c_8])).
% 1.79/1.18  tff(c_64, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_30, c_58])).
% 1.79/1.18  tff(c_65, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 1.79/1.18  tff(c_67, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_65])).
% 1.79/1.18  tff(c_22, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.18  tff(c_31, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_22])).
% 1.79/1.18  tff(c_68, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_31])).
% 1.79/1.18  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_68])).
% 1.79/1.18  tff(c_72, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_65])).
% 1.79/1.18  tff(c_12, plain, (![B_4]: (r1_tarski(k1_xboole_0, k1_tarski(B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.18  tff(c_77, plain, (![B_4]: (r1_tarski('#skF_1', k1_tarski(B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12])).
% 1.79/1.18  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_31])).
% 1.79/1.18  tff(c_85, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_22])).
% 1.79/1.18  tff(c_108, plain, (![B_15, A_16]: (k1_tarski(B_15)=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.18  tff(c_114, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_85, c_108])).
% 1.79/1.18  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_30, c_114])).
% 1.79/1.18  tff(c_128, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 1.79/1.18  tff(c_16, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.18  tff(c_137, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_16])).
% 1.79/1.18  tff(c_138, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_137])).
% 1.79/1.18  tff(c_141, plain, (![B_4]: (r1_tarski('#skF_1', k1_tarski(B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_12])).
% 1.79/1.18  tff(c_127, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_14])).
% 1.79/1.18  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_127])).
% 1.79/1.18  tff(c_150, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_137])).
% 1.79/1.18  tff(c_152, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_127])).
% 1.79/1.18  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_152])).
% 1.79/1.18  tff(c_157, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 1.79/1.18  tff(c_20, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.18  tff(c_165, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_157, c_20])).
% 1.79/1.18  tff(c_166, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_165])).
% 1.79/1.18  tff(c_158, plain, (![B_4]: (r1_tarski('#skF_3', k1_tarski(B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_12])).
% 1.79/1.18  tff(c_169, plain, (![B_4]: (r1_tarski('#skF_1', k1_tarski(B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_158])).
% 1.79/1.18  tff(c_156, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 1.79/1.18  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_156])).
% 1.79/1.18  tff(c_183, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_165])).
% 1.79/1.18  tff(c_185, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_156])).
% 1.79/1.18  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_185])).
% 1.79/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  Inference rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Ref     : 0
% 1.79/1.18  #Sup     : 27
% 1.79/1.18  #Fact    : 0
% 1.79/1.18  #Define  : 0
% 1.79/1.18  #Split   : 9
% 1.79/1.18  #Chain   : 0
% 1.79/1.18  #Close   : 0
% 1.79/1.19  
% 1.79/1.19  Ordering : KBO
% 1.79/1.19  
% 1.79/1.19  Simplification rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Subsume      : 5
% 1.79/1.19  #Demod        : 35
% 1.79/1.19  #Tautology    : 20
% 1.79/1.19  #SimpNegUnit  : 3
% 1.79/1.19  #BackRed      : 16
% 1.79/1.19  
% 1.79/1.19  #Partial instantiations: 0
% 1.79/1.19  #Strategies tried      : 1
% 1.79/1.19  
% 1.79/1.19  Timing (in seconds)
% 1.79/1.19  ----------------------
% 1.79/1.19  Preprocessing        : 0.27
% 1.79/1.19  Parsing              : 0.14
% 1.79/1.19  CNF conversion       : 0.02
% 1.79/1.19  Main loop            : 0.14
% 1.79/1.19  Inferencing          : 0.04
% 1.79/1.19  Reduction            : 0.05
% 1.79/1.19  Demodulation         : 0.04
% 1.79/1.19  BG Simplification    : 0.01
% 1.79/1.19  Subsumption          : 0.03
% 1.79/1.19  Abstraction          : 0.01
% 1.79/1.19  MUC search           : 0.00
% 1.79/1.19  Cooper               : 0.00
% 1.79/1.19  Total                : 0.45
% 1.79/1.19  Index Insertion      : 0.00
% 1.79/1.19  Index Deletion       : 0.00
% 1.79/1.19  Index Matching       : 0.00
% 1.79/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
