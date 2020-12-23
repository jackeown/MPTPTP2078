%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:10 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   57 (  80 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 126 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_375,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,B_89)
      | ~ r2_hidden(C_90,A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_415,plain,(
    ! [C_91] :
      ( ~ r2_hidden(C_91,'#skF_4')
      | ~ r2_hidden(C_91,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_375])).

tff(c_429,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_415])).

tff(c_32,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | r1_xboole_0(A_20,k3_xboole_0(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_41,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_92,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_92])).

tff(c_151,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_213,plain,(
    ! [B_63,A_64,C_65] :
      ( ~ r1_xboole_0(B_63,A_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_64,B_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_227,plain,(
    ! [C_65] :
      ( ~ r1_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3'))
      | ~ r2_hidden(C_65,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_213])).

tff(c_538,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_565,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_538])).

tff(c_595,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_565])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_595])).

tff(c_602,plain,(
    ! [C_110] : ~ r2_hidden(C_110,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_615,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_602])).

tff(c_51,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_523,plain,(
    ! [A_105,C_106,B_107] :
      ( ~ r1_xboole_0(A_105,C_106)
      | ~ r1_xboole_0(A_105,B_107)
      | r1_xboole_0(A_105,k2_xboole_0(B_107,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_898,plain,(
    ! [B_132,C_133,A_134] :
      ( r1_xboole_0(k2_xboole_0(B_132,C_133),A_134)
      | ~ r1_xboole_0(A_134,C_133)
      | ~ r1_xboole_0(A_134,B_132) ) ),
    inference(resolution,[status(thm)],[c_523,c_4])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_913,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_898,c_34])).

tff(c_921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_54,c_913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:36:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.54  
% 3.26/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.26/1.54  
% 3.26/1.54  %Foreground sorts:
% 3.26/1.54  
% 3.26/1.54  
% 3.26/1.54  %Background operators:
% 3.26/1.54  
% 3.26/1.54  
% 3.26/1.54  %Foreground operators:
% 3.26/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.26/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.54  
% 3.26/1.56  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.26/1.56  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.26/1.56  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.26/1.56  tff(f_100, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.26/1.56  tff(f_89, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.26/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.26/1.56  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.26/1.56  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.26/1.56  tff(f_83, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.26/1.56  tff(c_12, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.56  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.26/1.56  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.26/1.56  tff(c_375, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, B_89) | ~r2_hidden(C_90, A_88))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.26/1.56  tff(c_415, plain, (![C_91]: (~r2_hidden(C_91, '#skF_4') | ~r2_hidden(C_91, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_375])).
% 3.26/1.56  tff(c_429, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_415])).
% 3.26/1.56  tff(c_32, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.26/1.56  tff(c_24, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | r1_xboole_0(A_20, k3_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.26/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.56  tff(c_40, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.26/1.56  tff(c_41, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 3.26/1.56  tff(c_92, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.56  tff(c_96, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_41, c_92])).
% 3.26/1.56  tff(c_151, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.56  tff(c_213, plain, (![B_63, A_64, C_65]: (~r1_xboole_0(B_63, A_64) | ~r2_hidden(C_65, k3_xboole_0(A_64, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 3.26/1.56  tff(c_227, plain, (![C_65]: (~r1_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3')) | ~r2_hidden(C_65, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_213])).
% 3.26/1.56  tff(c_538, plain, (~r1_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_227])).
% 3.26/1.56  tff(c_565, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_24, c_538])).
% 3.26/1.56  tff(c_595, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_565])).
% 3.26/1.56  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_595])).
% 3.26/1.56  tff(c_602, plain, (![C_110]: (~r2_hidden(C_110, k3_xboole_0('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_227])).
% 3.26/1.56  tff(c_615, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_602])).
% 3.26/1.56  tff(c_51, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.56  tff(c_54, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_51])).
% 3.26/1.56  tff(c_523, plain, (![A_105, C_106, B_107]: (~r1_xboole_0(A_105, C_106) | ~r1_xboole_0(A_105, B_107) | r1_xboole_0(A_105, k2_xboole_0(B_107, C_106)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.26/1.56  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.56  tff(c_898, plain, (![B_132, C_133, A_134]: (r1_xboole_0(k2_xboole_0(B_132, C_133), A_134) | ~r1_xboole_0(A_134, C_133) | ~r1_xboole_0(A_134, B_132))), inference(resolution, [status(thm)], [c_523, c_4])).
% 3.26/1.56  tff(c_34, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.26/1.56  tff(c_913, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_898, c_34])).
% 3.26/1.56  tff(c_921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_615, c_54, c_913])).
% 3.26/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.56  
% 3.26/1.56  Inference rules
% 3.26/1.56  ----------------------
% 3.26/1.56  #Ref     : 0
% 3.26/1.56  #Sup     : 210
% 3.26/1.56  #Fact    : 0
% 3.26/1.56  #Define  : 0
% 3.26/1.56  #Split   : 3
% 3.26/1.56  #Chain   : 0
% 3.26/1.56  #Close   : 0
% 3.26/1.56  
% 3.26/1.56  Ordering : KBO
% 3.26/1.56  
% 3.26/1.56  Simplification rules
% 3.26/1.56  ----------------------
% 3.26/1.56  #Subsume      : 65
% 3.26/1.56  #Demod        : 58
% 3.26/1.56  #Tautology    : 78
% 3.26/1.56  #SimpNegUnit  : 8
% 3.26/1.56  #BackRed      : 0
% 3.26/1.56  
% 3.26/1.56  #Partial instantiations: 0
% 3.26/1.56  #Strategies tried      : 1
% 3.26/1.56  
% 3.26/1.56  Timing (in seconds)
% 3.26/1.56  ----------------------
% 3.26/1.56  Preprocessing        : 0.33
% 3.26/1.56  Parsing              : 0.18
% 3.26/1.56  CNF conversion       : 0.02
% 3.26/1.56  Main loop            : 0.45
% 3.26/1.56  Inferencing          : 0.16
% 3.26/1.56  Reduction            : 0.15
% 3.26/1.56  Demodulation         : 0.11
% 3.26/1.56  BG Simplification    : 0.02
% 3.26/1.56  Subsumption          : 0.10
% 3.26/1.56  Abstraction          : 0.02
% 3.26/1.56  MUC search           : 0.00
% 3.26/1.56  Cooper               : 0.00
% 3.26/1.56  Total                : 0.82
% 3.26/1.56  Index Insertion      : 0.00
% 3.26/1.56  Index Deletion       : 0.00
% 3.26/1.56  Index Matching       : 0.00
% 3.26/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
