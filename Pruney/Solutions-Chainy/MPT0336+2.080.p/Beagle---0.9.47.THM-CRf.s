%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:11 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 ( 130 expanded)
%              Number of equality atoms :    2 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_37,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_143,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_xboole_0(A_51,C_52)
      | ~ r1_xboole_0(B_53,C_52)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_437,plain,(
    ! [A_99,B_100,A_101] :
      ( r1_xboole_0(A_99,B_100)
      | ~ r1_tarski(A_99,k1_tarski(A_101))
      | r2_hidden(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_28,c_143])).

tff(c_441,plain,(
    ! [B_102] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_102)
      | r2_hidden('#skF_5',B_102) ) ),
    inference(resolution,[status(thm)],[c_37,c_437])).

tff(c_119,plain,(
    ! [A_47,B_48] :
      ( ~ r1_xboole_0(k3_xboole_0(A_47,B_48),B_48)
      | r1_xboole_0(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_126,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_466,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_126])).

tff(c_471,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_279,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_303,plain,(
    ! [C_73] :
      ( ~ r2_hidden(C_73,'#skF_3')
      | ~ r2_hidden(C_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_279])).

tff(c_480,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_471,c_303])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_480])).

tff(c_487,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_497,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_487,c_4])).

tff(c_80,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(B_29,A_30)
      | ~ r1_xboole_0(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_80])).

tff(c_333,plain,(
    ! [A_87,C_88,B_89] :
      ( ~ r1_xboole_0(A_87,C_88)
      | ~ r1_xboole_0(A_87,B_89)
      | r1_xboole_0(A_87,k2_xboole_0(B_89,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_641,plain,(
    ! [B_113,C_114,A_115] :
      ( r1_xboole_0(k2_xboole_0(B_113,C_114),A_115)
      | ~ r1_xboole_0(A_115,C_114)
      | ~ r1_xboole_0(A_115,B_113) ) ),
    inference(resolution,[status(thm)],[c_333,c_4])).

tff(c_30,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_658,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_641,c_30])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_83,c_658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.40  
% 2.98/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.98/1.40  
% 2.98/1.40  %Foreground sorts:
% 2.98/1.40  
% 2.98/1.40  
% 2.98/1.40  %Background operators:
% 2.98/1.40  
% 2.98/1.40  
% 2.98/1.40  %Foreground operators:
% 2.98/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.98/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.40  
% 2.98/1.41  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.98/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.98/1.41  tff(f_88, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.98/1.41  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.98/1.41  tff(f_77, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.98/1.41  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.98/1.41  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.98/1.41  tff(f_71, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.98/1.41  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.98/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.98/1.41  tff(c_36, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.98/1.41  tff(c_37, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.98/1.41  tff(c_28, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.98/1.41  tff(c_143, plain, (![A_51, C_52, B_53]: (r1_xboole_0(A_51, C_52) | ~r1_xboole_0(B_53, C_52) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.98/1.41  tff(c_437, plain, (![A_99, B_100, A_101]: (r1_xboole_0(A_99, B_100) | ~r1_tarski(A_99, k1_tarski(A_101)) | r2_hidden(A_101, B_100))), inference(resolution, [status(thm)], [c_28, c_143])).
% 2.98/1.41  tff(c_441, plain, (![B_102]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_102) | r2_hidden('#skF_5', B_102))), inference(resolution, [status(thm)], [c_37, c_437])).
% 2.98/1.41  tff(c_119, plain, (![A_47, B_48]: (~r1_xboole_0(k3_xboole_0(A_47, B_48), B_48) | r1_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.98/1.41  tff(c_126, plain, (![B_2, A_1]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), B_2) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 2.98/1.41  tff(c_466, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_441, c_126])).
% 2.98/1.41  tff(c_471, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_466])).
% 2.98/1.41  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.98/1.41  tff(c_279, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.98/1.41  tff(c_303, plain, (![C_73]: (~r2_hidden(C_73, '#skF_3') | ~r2_hidden(C_73, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_279])).
% 2.98/1.41  tff(c_480, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_471, c_303])).
% 2.98/1.41  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_480])).
% 2.98/1.41  tff(c_487, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_466])).
% 2.98/1.41  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.41  tff(c_497, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_487, c_4])).
% 2.98/1.41  tff(c_80, plain, (![B_29, A_30]: (r1_xboole_0(B_29, A_30) | ~r1_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.41  tff(c_83, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_80])).
% 2.98/1.41  tff(c_333, plain, (![A_87, C_88, B_89]: (~r1_xboole_0(A_87, C_88) | ~r1_xboole_0(A_87, B_89) | r1_xboole_0(A_87, k2_xboole_0(B_89, C_88)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.98/1.41  tff(c_641, plain, (![B_113, C_114, A_115]: (r1_xboole_0(k2_xboole_0(B_113, C_114), A_115) | ~r1_xboole_0(A_115, C_114) | ~r1_xboole_0(A_115, B_113))), inference(resolution, [status(thm)], [c_333, c_4])).
% 2.98/1.41  tff(c_30, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.98/1.41  tff(c_658, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_641, c_30])).
% 2.98/1.41  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_83, c_658])).
% 2.98/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.41  
% 2.98/1.41  Inference rules
% 2.98/1.41  ----------------------
% 2.98/1.41  #Ref     : 0
% 2.98/1.41  #Sup     : 148
% 2.98/1.41  #Fact    : 0
% 2.98/1.41  #Define  : 0
% 2.98/1.41  #Split   : 4
% 2.98/1.41  #Chain   : 0
% 2.98/1.41  #Close   : 0
% 2.98/1.41  
% 2.98/1.41  Ordering : KBO
% 2.98/1.41  
% 2.98/1.41  Simplification rules
% 2.98/1.41  ----------------------
% 2.98/1.41  #Subsume      : 20
% 2.98/1.41  #Demod        : 9
% 2.98/1.41  #Tautology    : 21
% 2.98/1.41  #SimpNegUnit  : 0
% 2.98/1.41  #BackRed      : 0
% 2.98/1.41  
% 2.98/1.41  #Partial instantiations: 0
% 2.98/1.41  #Strategies tried      : 1
% 2.98/1.41  
% 2.98/1.41  Timing (in seconds)
% 2.98/1.41  ----------------------
% 2.98/1.41  Preprocessing        : 0.31
% 2.98/1.41  Parsing              : 0.17
% 2.98/1.41  CNF conversion       : 0.02
% 2.98/1.41  Main loop            : 0.34
% 2.98/1.41  Inferencing          : 0.13
% 2.98/1.41  Reduction            : 0.09
% 2.98/1.41  Demodulation         : 0.07
% 2.98/1.41  BG Simplification    : 0.02
% 2.98/1.42  Subsumption          : 0.08
% 2.98/1.42  Abstraction          : 0.02
% 2.98/1.42  MUC search           : 0.00
% 2.98/1.42  Cooper               : 0.00
% 2.98/1.42  Total                : 0.68
% 2.98/1.42  Index Insertion      : 0.00
% 2.98/1.42  Index Deletion       : 0.00
% 2.98/1.42  Index Matching       : 0.00
% 2.98/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
