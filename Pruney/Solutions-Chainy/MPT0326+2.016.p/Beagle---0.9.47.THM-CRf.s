%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:30 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 106 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 196 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_70,plain,(
    ! [B_26,D_27,A_28,C_29] :
      ( r1_tarski(B_26,D_27)
      | k2_zfmisc_1(A_28,B_26) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_28,B_26),k2_zfmisc_1(C_29,D_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_70])).

tff(c_88,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_73])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_8])).

tff(c_111,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_xboole_0(A_21,B_22)
      | ~ r1_tarski(C_23,B_22)
      | ~ r1_tarski(C_23,A_21)
      | v1_xboole_0(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [C_24,A_25] :
      ( ~ r1_tarski(C_24,k1_xboole_0)
      | ~ r1_tarski(C_24,A_25)
      | v1_xboole_0(C_24) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_65,plain,(
    ! [A_25] :
      ( ~ r1_tarski(k1_xboole_0,A_25)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_140,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_68])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_140])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_159,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_2])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_18])).

tff(c_176,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_178,plain,(
    ! [A_35,C_36,B_37,D_38] :
      ( r1_tarski(A_35,C_36)
      | k2_zfmisc_1(A_35,B_37) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_35,B_37),k2_zfmisc_1(C_36,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_176,c_178])).

tff(c_196,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_181])).

tff(c_217,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_8])).

tff(c_219,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_227,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_18])).

tff(c_236,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_240,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_68])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:34:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.28  
% 1.89/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.28  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.89/1.28  
% 1.89/1.28  %Foreground sorts:
% 1.89/1.28  
% 1.89/1.28  
% 1.89/1.28  %Background operators:
% 1.89/1.28  
% 1.89/1.28  
% 1.89/1.28  %Foreground operators:
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.28  
% 1.89/1.29  tff(f_64, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 1.89/1.29  tff(f_53, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 1.89/1.29  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.89/1.29  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.89/1.29  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.89/1.29  tff(f_39, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.89/1.29  tff(c_22, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.29  tff(c_18, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.29  tff(c_20, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.29  tff(c_69, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_20])).
% 1.89/1.29  tff(c_70, plain, (![B_26, D_27, A_28, C_29]: (r1_tarski(B_26, D_27) | k2_zfmisc_1(A_28, B_26)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_28, B_26), k2_zfmisc_1(C_29, D_27)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.29  tff(c_73, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_70])).
% 1.89/1.29  tff(c_88, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_73])).
% 1.89/1.29  tff(c_8, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.29  tff(c_109, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_88, c_8])).
% 1.89/1.29  tff(c_111, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_109])).
% 1.89/1.29  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.29  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.29  tff(c_58, plain, (![A_21, B_22, C_23]: (~r1_xboole_0(A_21, B_22) | ~r1_tarski(C_23, B_22) | ~r1_tarski(C_23, A_21) | v1_xboole_0(C_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.29  tff(c_62, plain, (![C_24, A_25]: (~r1_tarski(C_24, k1_xboole_0) | ~r1_tarski(C_24, A_25) | v1_xboole_0(C_24))), inference(resolution, [status(thm)], [c_4, c_58])).
% 1.89/1.29  tff(c_65, plain, (![A_25]: (~r1_tarski(k1_xboole_0, A_25) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_62])).
% 1.89/1.29  tff(c_68, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_65])).
% 1.89/1.29  tff(c_140, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_68])).
% 1.89/1.29  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_140])).
% 1.89/1.29  tff(c_149, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_109])).
% 1.89/1.29  tff(c_159, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_2])).
% 1.89/1.29  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_18])).
% 1.89/1.29  tff(c_176, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 1.89/1.29  tff(c_178, plain, (![A_35, C_36, B_37, D_38]: (r1_tarski(A_35, C_36) | k2_zfmisc_1(A_35, B_37)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_35, B_37), k2_zfmisc_1(C_36, D_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.29  tff(c_181, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_176, c_178])).
% 1.89/1.29  tff(c_196, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_181])).
% 1.89/1.29  tff(c_217, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_196, c_8])).
% 1.89/1.29  tff(c_219, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_217])).
% 1.89/1.29  tff(c_227, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_2])).
% 1.89/1.29  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_18])).
% 1.89/1.29  tff(c_236, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_217])).
% 1.89/1.29  tff(c_240, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_68])).
% 1.89/1.29  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_240])).
% 1.89/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.29  
% 1.89/1.29  Inference rules
% 1.89/1.29  ----------------------
% 1.89/1.29  #Ref     : 0
% 1.89/1.29  #Sup     : 43
% 1.89/1.29  #Fact    : 0
% 1.89/1.29  #Define  : 0
% 1.89/1.29  #Split   : 3
% 1.89/1.29  #Chain   : 0
% 1.89/1.29  #Close   : 0
% 1.89/1.29  
% 1.89/1.29  Ordering : KBO
% 1.89/1.29  
% 1.89/1.29  Simplification rules
% 1.89/1.29  ----------------------
% 1.89/1.29  #Subsume      : 0
% 1.89/1.29  #Demod        : 82
% 1.89/1.29  #Tautology    : 29
% 1.89/1.29  #SimpNegUnit  : 4
% 1.89/1.29  #BackRed      : 42
% 1.89/1.29  
% 1.89/1.29  #Partial instantiations: 0
% 1.89/1.29  #Strategies tried      : 1
% 1.89/1.29  
% 1.89/1.29  Timing (in seconds)
% 1.89/1.29  ----------------------
% 1.89/1.29  Preprocessing        : 0.29
% 1.89/1.29  Parsing              : 0.16
% 1.89/1.29  CNF conversion       : 0.02
% 1.89/1.29  Main loop            : 0.18
% 1.89/1.29  Inferencing          : 0.06
% 1.89/1.29  Reduction            : 0.06
% 1.89/1.29  Demodulation         : 0.05
% 1.89/1.29  BG Simplification    : 0.02
% 1.89/1.29  Subsumption          : 0.03
% 1.89/1.30  Abstraction          : 0.01
% 1.89/1.30  MUC search           : 0.00
% 1.89/1.30  Cooper               : 0.00
% 1.89/1.30  Total                : 0.50
% 1.89/1.30  Index Insertion      : 0.00
% 1.89/1.30  Index Deletion       : 0.00
% 1.89/1.30  Index Matching       : 0.00
% 1.89/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
