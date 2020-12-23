%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:30 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 100 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 188 expanded)
%              Number of equality atoms :   23 (  56 expanded)
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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3'))
    | r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_61,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_73,plain,(
    ! [B_22,D_23,A_24,C_25] :
      ( r1_tarski(B_22,D_23)
      | k2_zfmisc_1(A_24,B_22) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_24,B_22),k2_zfmisc_1(C_25,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_73])).

tff(c_91,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_76])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ! [B_18,A_19] :
      ( ~ r1_xboole_0(B_18,A_19)
      | ~ r1_tarski(B_18,A_19)
      | v1_xboole_0(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_57])).

tff(c_144,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_60])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_144])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_162,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_20])).

tff(c_180,plain,(
    r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_193,plain,(
    ! [A_32,C_33,B_34,D_35] :
      ( r1_tarski(A_32,C_33)
      | k2_zfmisc_1(A_32,B_34) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_32,B_34),k2_zfmisc_1(C_33,D_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_196,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_193])).

tff(c_211,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_196])).

tff(c_232,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_10])).

tff(c_234,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_242,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_2])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_20])).

tff(c_251,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_256,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_60])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.21  
% 1.87/1.21  %Foreground sorts:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Background operators:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Foreground operators:
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.21  
% 1.87/1.22  tff(f_72, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 1.87/1.22  tff(f_61, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 1.87/1.22  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.87/1.22  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.87/1.22  tff(f_39, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.87/1.22  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.87/1.22  tff(c_24, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.22  tff(c_20, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.22  tff(c_22, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3')) | r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.87/1.22  tff(c_61, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_22])).
% 1.87/1.22  tff(c_73, plain, (![B_22, D_23, A_24, C_25]: (r1_tarski(B_22, D_23) | k2_zfmisc_1(A_24, B_22)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_24, B_22), k2_zfmisc_1(C_25, D_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.87/1.22  tff(c_76, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_73])).
% 1.87/1.22  tff(c_91, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_76])).
% 1.87/1.22  tff(c_10, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.87/1.22  tff(c_112, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_91, c_10])).
% 1.87/1.22  tff(c_114, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_112])).
% 1.87/1.22  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.22  tff(c_4, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.22  tff(c_54, plain, (![B_18, A_19]: (~r1_xboole_0(B_18, A_19) | ~r1_tarski(B_18, A_19) | v1_xboole_0(B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.22  tff(c_57, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_54])).
% 1.87/1.22  tff(c_60, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_57])).
% 1.87/1.22  tff(c_144, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_60])).
% 1.87/1.22  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_144])).
% 1.87/1.22  tff(c_152, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_112])).
% 1.87/1.22  tff(c_162, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2])).
% 1.87/1.22  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_20])).
% 1.87/1.22  tff(c_180, plain, (r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_22])).
% 1.87/1.22  tff(c_193, plain, (![A_32, C_33, B_34, D_35]: (r1_tarski(A_32, C_33) | k2_zfmisc_1(A_32, B_34)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_32, B_34), k2_zfmisc_1(C_33, D_35)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.87/1.22  tff(c_196, plain, (r1_tarski('#skF_2', '#skF_4') | k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_180, c_193])).
% 1.87/1.22  tff(c_211, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_196])).
% 1.87/1.22  tff(c_232, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_211, c_10])).
% 1.87/1.22  tff(c_234, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_232])).
% 1.87/1.22  tff(c_242, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_2])).
% 1.87/1.22  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_20])).
% 1.87/1.22  tff(c_251, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_232])).
% 1.87/1.22  tff(c_256, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_60])).
% 1.87/1.22  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_256])).
% 1.87/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  Inference rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Ref     : 0
% 1.87/1.22  #Sup     : 45
% 1.87/1.22  #Fact    : 0
% 1.87/1.22  #Define  : 0
% 1.87/1.22  #Split   : 3
% 1.87/1.22  #Chain   : 0
% 1.87/1.22  #Close   : 0
% 1.87/1.22  
% 1.87/1.22  Ordering : KBO
% 1.87/1.22  
% 1.87/1.22  Simplification rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Subsume      : 0
% 1.87/1.22  #Demod        : 87
% 1.87/1.22  #Tautology    : 33
% 1.87/1.22  #SimpNegUnit  : 4
% 1.87/1.22  #BackRed      : 42
% 1.87/1.22  
% 1.87/1.22  #Partial instantiations: 0
% 1.87/1.22  #Strategies tried      : 1
% 1.87/1.22  
% 1.87/1.22  Timing (in seconds)
% 1.87/1.22  ----------------------
% 1.87/1.22  Preprocessing        : 0.28
% 1.87/1.22  Parsing              : 0.16
% 1.87/1.22  CNF conversion       : 0.02
% 1.87/1.22  Main loop            : 0.18
% 1.87/1.22  Inferencing          : 0.06
% 1.87/1.22  Reduction            : 0.06
% 1.87/1.22  Demodulation         : 0.04
% 1.87/1.22  BG Simplification    : 0.01
% 1.87/1.22  Subsumption          : 0.03
% 1.87/1.22  Abstraction          : 0.01
% 1.87/1.22  MUC search           : 0.00
% 1.87/1.22  Cooper               : 0.00
% 1.87/1.22  Total                : 0.48
% 1.87/1.22  Index Insertion      : 0.00
% 1.87/1.22  Index Deletion       : 0.00
% 1.87/1.22  Index Matching       : 0.00
% 1.87/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
