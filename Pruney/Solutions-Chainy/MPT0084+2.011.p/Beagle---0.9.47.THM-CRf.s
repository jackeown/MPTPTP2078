%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:05 EST 2020

% Result     : Theorem 11.15s
% Output     : CNFRefutation 11.15s
% Verified   : 
% Statistics : Number of formulae       :   58 (  82 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 113 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_114,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_123,plain,(
    ! [A_34,B_35] : r1_tarski(k3_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_378,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),k3_xboole_0(A_55,B_56))
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_399,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(B_2,A_1))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_378])).

tff(c_16,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_223,plain,(
    ! [A_47,B_48] : k3_xboole_0(k4_xboole_0(A_47,B_48),A_47) = k4_xboole_0(A_47,B_48) ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_250,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(k3_xboole_0(A_18,B_19),A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_223])).

tff(c_842,plain,(
    ! [A_75,B_76] : k3_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_250])).

tff(c_924,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_842])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_501,plain,(
    ! [A_62,C_63,B_64,D_65] :
      ( r1_tarski(k3_xboole_0(A_62,C_63),k3_xboole_0(B_64,D_65))
      | ~ r1_tarski(C_63,D_65)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2405,plain,(
    ! [A_99,B_100,B_101,D_102] :
      ( r1_tarski(k3_xboole_0(A_99,B_100),k3_xboole_0(B_101,D_102))
      | ~ r1_tarski(A_99,D_102)
      | ~ r1_tarski(B_100,B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_501])).

tff(c_20,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_25,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_27,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_25,c_27])).

tff(c_193,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_xboole_0(A_40,C_41)
      | ~ r1_xboole_0(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,(
    ! [A_40] :
      ( r1_xboole_0(A_40,'#skF_2')
      | ~ r1_tarski(A_40,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_19392,plain,(
    ! [A_390,B_391] :
      ( r1_xboole_0(k3_xboole_0(A_390,B_391),'#skF_2')
      | ~ r1_tarski(A_390,'#skF_3')
      | ~ r1_tarski(B_391,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2405,c_198])).

tff(c_132,plain,(
    ! [A_36,B_37] : r1_tarski(k3_xboole_0(A_36,B_37),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_14])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1097,plain,(
    ! [A_83,B_84] : k3_xboole_0(k3_xboole_0(A_83,B_84),A_83) = k3_xboole_0(A_83,B_84) ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3313,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ r1_xboole_0(k3_xboole_0(A_127,B_128),A_127)
      | ~ r2_hidden(C_129,k3_xboole_0(A_127,B_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1097,c_8])).

tff(c_3357,plain,(
    ! [B_2,A_1,C_129] :
      ( ~ r1_xboole_0(k3_xboole_0(B_2,A_1),A_1)
      | ~ r2_hidden(C_129,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3313])).

tff(c_19401,plain,(
    ! [C_129,A_390] :
      ( ~ r2_hidden(C_129,k3_xboole_0('#skF_2',A_390))
      | ~ r1_tarski(A_390,'#skF_3')
      | ~ r1_tarski('#skF_2','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_19392,c_3357])).

tff(c_19737,plain,(
    ! [C_398,A_399] :
      ( ~ r2_hidden(C_398,k3_xboole_0('#skF_2',A_399))
      | ~ r1_tarski(A_399,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_19401])).

tff(c_24280,plain,(
    ! [C_468,B_469] :
      ( ~ r2_hidden(C_468,k3_xboole_0('#skF_2',B_469))
      | ~ r1_tarski(k3_xboole_0(B_469,'#skF_2'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_19737])).

tff(c_24354,plain,(
    ! [A_470] :
      ( ~ r1_tarski(k3_xboole_0(A_470,'#skF_2'),'#skF_3')
      | r1_xboole_0(A_470,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_399,c_24280])).

tff(c_24408,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_24354])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24413,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24408,c_4])).

tff(c_24418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n017.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 20:44:16 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.15/4.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.15/4.89  
% 11.15/4.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.15/4.89  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.15/4.89  
% 11.15/4.89  %Foreground sorts:
% 11.15/4.89  
% 11.15/4.89  
% 11.15/4.89  %Background operators:
% 11.15/4.89  
% 11.15/4.89  
% 11.15/4.89  %Foreground operators:
% 11.15/4.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.15/4.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.15/4.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.15/4.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.15/4.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.15/4.89  tff('#skF_2', type, '#skF_2': $i).
% 11.15/4.89  tff('#skF_3', type, '#skF_3': $i).
% 11.15/4.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.15/4.89  tff('#skF_4', type, '#skF_4': $i).
% 11.15/4.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.15/4.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.15/4.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.15/4.89  
% 11.15/4.91  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 11.15/4.91  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.15/4.91  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.15/4.91  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.15/4.91  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.15/4.91  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.15/4.91  tff(f_51, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 11.15/4.91  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.15/4.91  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.15/4.91  tff(c_24, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.15/4.91  tff(c_114, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.15/4.91  tff(c_14, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.15/4.91  tff(c_123, plain, (![A_34, B_35]: (r1_tarski(k3_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_114, c_14])).
% 11.15/4.91  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.15/4.91  tff(c_378, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), k3_xboole_0(A_55, B_56)) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.15/4.91  tff(c_399, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(B_2, A_1)) | r1_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_378])).
% 11.15/4.91  tff(c_16, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.15/4.91  tff(c_68, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.15/4.91  tff(c_223, plain, (![A_47, B_48]: (k3_xboole_0(k4_xboole_0(A_47, B_48), A_47)=k4_xboole_0(A_47, B_48))), inference(resolution, [status(thm)], [c_14, c_68])).
% 11.15/4.91  tff(c_250, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(k3_xboole_0(A_18, B_19), A_18))), inference(superposition, [status(thm), theory('equality')], [c_16, c_223])).
% 11.15/4.91  tff(c_842, plain, (![A_75, B_76]: (k3_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_250])).
% 11.15/4.91  tff(c_924, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_842])).
% 11.15/4.91  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.15/4.91  tff(c_501, plain, (![A_62, C_63, B_64, D_65]: (r1_tarski(k3_xboole_0(A_62, C_63), k3_xboole_0(B_64, D_65)) | ~r1_tarski(C_63, D_65) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.15/4.91  tff(c_2405, plain, (![A_99, B_100, B_101, D_102]: (r1_tarski(k3_xboole_0(A_99, B_100), k3_xboole_0(B_101, D_102)) | ~r1_tarski(A_99, D_102) | ~r1_tarski(B_100, B_101))), inference(superposition, [status(thm), theory('equality')], [c_2, c_501])).
% 11.15/4.91  tff(c_20, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.15/4.91  tff(c_25, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 11.15/4.91  tff(c_27, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.15/4.91  tff(c_30, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_25, c_27])).
% 11.15/4.91  tff(c_193, plain, (![A_40, C_41, B_42]: (r1_xboole_0(A_40, C_41) | ~r1_xboole_0(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.15/4.91  tff(c_198, plain, (![A_40]: (r1_xboole_0(A_40, '#skF_2') | ~r1_tarski(A_40, k3_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_193])).
% 11.15/4.91  tff(c_19392, plain, (![A_390, B_391]: (r1_xboole_0(k3_xboole_0(A_390, B_391), '#skF_2') | ~r1_tarski(A_390, '#skF_3') | ~r1_tarski(B_391, '#skF_4'))), inference(resolution, [status(thm)], [c_2405, c_198])).
% 11.15/4.91  tff(c_132, plain, (![A_36, B_37]: (r1_tarski(k3_xboole_0(A_36, B_37), A_36))), inference(superposition, [status(thm), theory('equality')], [c_114, c_14])).
% 11.15/4.91  tff(c_12, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.15/4.91  tff(c_1097, plain, (![A_83, B_84]: (k3_xboole_0(k3_xboole_0(A_83, B_84), A_83)=k3_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_132, c_12])).
% 11.15/4.91  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.15/4.91  tff(c_3313, plain, (![A_127, B_128, C_129]: (~r1_xboole_0(k3_xboole_0(A_127, B_128), A_127) | ~r2_hidden(C_129, k3_xboole_0(A_127, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_1097, c_8])).
% 11.15/4.91  tff(c_3357, plain, (![B_2, A_1, C_129]: (~r1_xboole_0(k3_xboole_0(B_2, A_1), A_1) | ~r2_hidden(C_129, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3313])).
% 11.15/4.91  tff(c_19401, plain, (![C_129, A_390]: (~r2_hidden(C_129, k3_xboole_0('#skF_2', A_390)) | ~r1_tarski(A_390, '#skF_3') | ~r1_tarski('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_19392, c_3357])).
% 11.15/4.91  tff(c_19737, plain, (![C_398, A_399]: (~r2_hidden(C_398, k3_xboole_0('#skF_2', A_399)) | ~r1_tarski(A_399, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_19401])).
% 11.15/4.91  tff(c_24280, plain, (![C_468, B_469]: (~r2_hidden(C_468, k3_xboole_0('#skF_2', B_469)) | ~r1_tarski(k3_xboole_0(B_469, '#skF_2'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_924, c_19737])).
% 11.15/4.91  tff(c_24354, plain, (![A_470]: (~r1_tarski(k3_xboole_0(A_470, '#skF_2'), '#skF_3') | r1_xboole_0(A_470, '#skF_2'))), inference(resolution, [status(thm)], [c_399, c_24280])).
% 11.15/4.91  tff(c_24408, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_123, c_24354])).
% 11.15/4.91  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.15/4.91  tff(c_24413, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24408, c_4])).
% 11.15/4.91  tff(c_24418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_24413])).
% 11.15/4.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.15/4.91  
% 11.15/4.91  Inference rules
% 11.15/4.91  ----------------------
% 11.15/4.91  #Ref     : 0
% 11.15/4.91  #Sup     : 6503
% 11.15/4.91  #Fact    : 0
% 11.15/4.91  #Define  : 0
% 11.15/4.91  #Split   : 13
% 11.15/4.91  #Chain   : 0
% 11.15/4.91  #Close   : 0
% 11.15/4.91  
% 11.15/4.91  Ordering : KBO
% 11.15/4.91  
% 11.15/4.91  Simplification rules
% 11.15/4.91  ----------------------
% 11.15/4.91  #Subsume      : 1703
% 11.15/4.91  #Demod        : 4482
% 11.15/4.91  #Tautology    : 1896
% 11.15/4.91  #SimpNegUnit  : 97
% 11.15/4.91  #BackRed      : 3
% 11.15/4.91  
% 11.15/4.91  #Partial instantiations: 0
% 11.15/4.91  #Strategies tried      : 1
% 11.15/4.91  
% 11.15/4.91  Timing (in seconds)
% 11.15/4.91  ----------------------
% 11.15/4.91  Preprocessing        : 0.26
% 11.15/4.91  Parsing              : 0.14
% 11.15/4.91  CNF conversion       : 0.02
% 11.15/4.91  Main loop            : 3.90
% 11.15/4.91  Inferencing          : 0.67
% 11.15/4.91  Reduction            : 1.96
% 11.15/4.91  Demodulation         : 1.72
% 11.15/4.91  BG Simplification    : 0.08
% 11.15/4.91  Subsumption          : 0.98
% 11.15/4.91  Abstraction          : 0.12
% 11.15/4.91  MUC search           : 0.00
% 11.15/4.91  Cooper               : 0.00
% 11.15/4.91  Total                : 4.19
% 11.15/4.91  Index Insertion      : 0.00
% 11.15/4.91  Index Deletion       : 0.00
% 11.15/4.91  Index Matching       : 0.00
% 11.15/4.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
