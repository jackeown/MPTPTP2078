%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:11 EST 2020

% Result     : Theorem 6.33s
% Output     : CNFRefutation 6.49s
% Verified   : 
% Statistics : Number of formulae       :   64 (  84 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 108 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_24,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    ! [A_37,B_38] : r1_tarski(k4_xboole_0(A_37,B_38),A_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [A_23] : r1_tarski(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_53])).

tff(c_38,plain,(
    ! [A_32,C_34,B_33] :
      ( r1_xboole_0(A_32,k4_xboole_0(C_34,B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2323,plain,(
    ! [A_162,B_163] :
      ( k3_xboole_0(A_162,B_163) = A_162
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2339,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_2323])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2422,plain,(
    ! [A_166,B_167] : k2_xboole_0(k3_xboole_0(A_166,B_167),k4_xboole_0(A_166,B_167)) = A_166 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7157,plain,(
    ! [B_317,A_318] : k2_xboole_0(k3_xboole_0(B_317,A_318),k4_xboole_0(A_318,B_317)) = A_318 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2422])).

tff(c_7292,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_2')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2339,c_7157])).

tff(c_36,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_xboole_0(A_29,B_30)
      | ~ r1_xboole_0(A_29,k2_xboole_0(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10307,plain,(
    ! [A_388] :
      ( r1_xboole_0(A_388,'#skF_2')
      | ~ r1_xboole_0(A_388,k4_xboole_0('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_36])).

tff(c_10359,plain,(
    ! [A_389] :
      ( r1_xboole_0(A_389,'#skF_2')
      | ~ r1_tarski(A_389,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_10307])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),k3_xboole_0(A_7,B_8))
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2687,plain,(
    ! [A_178,B_179,C_180] :
      ( ~ r1_xboole_0(A_178,B_179)
      | ~ r2_hidden(C_180,k3_xboole_0(A_178,B_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5269,plain,(
    ! [B_263,A_264,C_265] :
      ( ~ r1_xboole_0(B_263,A_264)
      | ~ r2_hidden(C_265,k3_xboole_0(A_264,B_263)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2687])).

tff(c_5309,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_5269])).

tff(c_10379,plain,(
    ! [A_390] :
      ( r1_xboole_0('#skF_2',A_390)
      | ~ r1_tarski(A_390,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10359,c_5309])).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_124,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_28,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_126,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_138,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_126])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_276,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(k2_xboole_0(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_288,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(A_62,B_63)) ),
    inference(resolution,[status(thm)],[c_56,c_276])).

tff(c_16,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,C_16)
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1341,plain,(
    ! [A_110,B_111,B_112] : r1_tarski(A_110,k2_xboole_0(k2_xboole_0(A_110,B_111),B_112)) ),
    inference(resolution,[status(thm)],[c_288,c_16])).

tff(c_1504,plain,(
    ! [A_118,B_119,B_120] : r1_tarski(k3_xboole_0(A_118,B_119),k2_xboole_0(A_118,B_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1341])).

tff(c_1861,plain,(
    ! [A_136,B_137,B_138] : r1_tarski(k3_xboole_0(A_136,B_137),k2_xboole_0(B_137,B_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1504])).

tff(c_2158,plain,(
    ! [A_151,A_152,B_153] : r1_tarski(k3_xboole_0(A_151,A_152),k2_xboole_0(B_153,A_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1861])).

tff(c_2273,plain,(
    ! [B_157] : r1_tarski('#skF_2',k2_xboole_0(B_157,k4_xboole_0('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_2158])).

tff(c_2288,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2273])).

tff(c_2305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_2288])).

tff(c_2306,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_10415,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_10379,c_2306])).

tff(c_10431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:06:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.33/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.33  
% 6.33/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.33/2.33  
% 6.33/2.33  %Foreground sorts:
% 6.33/2.33  
% 6.33/2.33  
% 6.33/2.33  %Background operators:
% 6.33/2.33  
% 6.33/2.33  
% 6.33/2.33  %Foreground operators:
% 6.33/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.33/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.33/2.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.33/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.33/2.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.33/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.33/2.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.33/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.33/2.33  tff('#skF_3', type, '#skF_3': $i).
% 6.33/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.33/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.33/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.33/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.33/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.33/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.33/2.33  
% 6.49/2.35  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.49/2.35  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.49/2.35  tff(f_89, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.49/2.35  tff(f_96, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.49/2.35  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.49/2.35  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.49/2.35  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.49/2.35  tff(f_85, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.49/2.35  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.49/2.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.49/2.35  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.49/2.35  tff(c_24, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.49/2.35  tff(c_53, plain, (![A_37, B_38]: (r1_tarski(k4_xboole_0(A_37, B_38), A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.49/2.35  tff(c_56, plain, (![A_23]: (r1_tarski(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_24, c_53])).
% 6.49/2.35  tff(c_38, plain, (![A_32, C_34, B_33]: (r1_xboole_0(A_32, k4_xboole_0(C_34, B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.49/2.35  tff(c_42, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.35  tff(c_2323, plain, (![A_162, B_163]: (k3_xboole_0(A_162, B_163)=A_162 | ~r1_tarski(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.49/2.35  tff(c_2339, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_42, c_2323])).
% 6.49/2.35  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.49/2.35  tff(c_2422, plain, (![A_166, B_167]: (k2_xboole_0(k3_xboole_0(A_166, B_167), k4_xboole_0(A_166, B_167))=A_166)), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.49/2.35  tff(c_7157, plain, (![B_317, A_318]: (k2_xboole_0(k3_xboole_0(B_317, A_318), k4_xboole_0(A_318, B_317))=A_318)), inference(superposition, [status(thm), theory('equality')], [c_4, c_2422])).
% 6.49/2.35  tff(c_7292, plain, (k2_xboole_0('#skF_2', k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_2'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2339, c_7157])).
% 6.49/2.35  tff(c_36, plain, (![A_29, B_30, C_31]: (r1_xboole_0(A_29, B_30) | ~r1_xboole_0(A_29, k2_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.49/2.35  tff(c_10307, plain, (![A_388]: (r1_xboole_0(A_388, '#skF_2') | ~r1_xboole_0(A_388, k4_xboole_0('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_7292, c_36])).
% 6.49/2.35  tff(c_10359, plain, (![A_389]: (r1_xboole_0(A_389, '#skF_2') | ~r1_tarski(A_389, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_10307])).
% 6.49/2.35  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), k3_xboole_0(A_7, B_8)) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.49/2.35  tff(c_2687, plain, (![A_178, B_179, C_180]: (~r1_xboole_0(A_178, B_179) | ~r2_hidden(C_180, k3_xboole_0(A_178, B_179)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.49/2.35  tff(c_5269, plain, (![B_263, A_264, C_265]: (~r1_xboole_0(B_263, A_264) | ~r2_hidden(C_265, k3_xboole_0(A_264, B_263)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2687])).
% 6.49/2.35  tff(c_5309, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | r1_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_10, c_5269])).
% 6.49/2.35  tff(c_10379, plain, (![A_390]: (r1_xboole_0('#skF_2', A_390) | ~r1_tarski(A_390, '#skF_4'))), inference(resolution, [status(thm)], [c_10359, c_5309])).
% 6.49/2.35  tff(c_40, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.35  tff(c_124, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 6.49/2.35  tff(c_28, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.49/2.35  tff(c_126, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.49/2.35  tff(c_138, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_42, c_126])).
% 6.49/2.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.49/2.35  tff(c_276, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(k2_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.49/2.35  tff(c_288, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(A_62, B_63)))), inference(resolution, [status(thm)], [c_56, c_276])).
% 6.49/2.35  tff(c_16, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, C_16) | ~r1_tarski(k2_xboole_0(A_14, B_15), C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.49/2.35  tff(c_1341, plain, (![A_110, B_111, B_112]: (r1_tarski(A_110, k2_xboole_0(k2_xboole_0(A_110, B_111), B_112)))), inference(resolution, [status(thm)], [c_288, c_16])).
% 6.49/2.35  tff(c_1504, plain, (![A_118, B_119, B_120]: (r1_tarski(k3_xboole_0(A_118, B_119), k2_xboole_0(A_118, B_120)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1341])).
% 6.49/2.35  tff(c_1861, plain, (![A_136, B_137, B_138]: (r1_tarski(k3_xboole_0(A_136, B_137), k2_xboole_0(B_137, B_138)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1504])).
% 6.49/2.35  tff(c_2158, plain, (![A_151, A_152, B_153]: (r1_tarski(k3_xboole_0(A_151, A_152), k2_xboole_0(B_153, A_152)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1861])).
% 6.49/2.35  tff(c_2273, plain, (![B_157]: (r1_tarski('#skF_2', k2_xboole_0(B_157, k4_xboole_0('#skF_3', '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_138, c_2158])).
% 6.49/2.35  tff(c_2288, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2273])).
% 6.49/2.35  tff(c_2305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_2288])).
% 6.49/2.35  tff(c_2306, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 6.49/2.35  tff(c_10415, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_10379, c_2306])).
% 6.49/2.35  tff(c_10431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_10415])).
% 6.49/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.35  
% 6.49/2.35  Inference rules
% 6.49/2.35  ----------------------
% 6.49/2.35  #Ref     : 0
% 6.49/2.35  #Sup     : 2571
% 6.49/2.35  #Fact    : 0
% 6.49/2.35  #Define  : 0
% 6.49/2.35  #Split   : 6
% 6.49/2.35  #Chain   : 0
% 6.49/2.35  #Close   : 0
% 6.49/2.35  
% 6.49/2.35  Ordering : KBO
% 6.49/2.35  
% 6.49/2.35  Simplification rules
% 6.49/2.35  ----------------------
% 6.49/2.35  #Subsume      : 238
% 6.49/2.35  #Demod        : 1783
% 6.49/2.35  #Tautology    : 1728
% 6.49/2.35  #SimpNegUnit  : 39
% 6.49/2.35  #BackRed      : 17
% 6.49/2.35  
% 6.49/2.35  #Partial instantiations: 0
% 6.49/2.35  #Strategies tried      : 1
% 6.49/2.35  
% 6.49/2.35  Timing (in seconds)
% 6.49/2.35  ----------------------
% 6.49/2.35  Preprocessing        : 0.30
% 6.49/2.35  Parsing              : 0.17
% 6.49/2.35  CNF conversion       : 0.02
% 6.49/2.35  Main loop            : 1.28
% 6.49/2.35  Inferencing          : 0.38
% 6.49/2.35  Reduction            : 0.56
% 6.49/2.35  Demodulation         : 0.45
% 6.49/2.35  BG Simplification    : 0.04
% 6.49/2.35  Subsumption          : 0.21
% 6.49/2.35  Abstraction          : 0.05
% 6.49/2.35  MUC search           : 0.00
% 6.49/2.35  Cooper               : 0.00
% 6.49/2.35  Total                : 1.60
% 6.49/2.35  Index Insertion      : 0.00
% 6.49/2.35  Index Deletion       : 0.00
% 6.49/2.35  Index Matching       : 0.00
% 6.49/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
