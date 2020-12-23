%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 10.61s
% Output     : CNFRefutation 10.61s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 (  74 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_82,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_62,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_40,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),A_14)
      | r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_211,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_4'(A_63,B_64),B_64)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3386,plain,(
    ! [A_186,A_187,B_188] :
      ( ~ r2_hidden('#skF_4'(A_186,k4_xboole_0(A_187,B_188)),B_188)
      | r1_xboole_0(A_186,k4_xboole_0(A_187,B_188)) ) ),
    inference(resolution,[status(thm)],[c_211,c_12])).

tff(c_3438,plain,(
    ! [A_189,A_190] : r1_xboole_0(A_189,k4_xboole_0(A_190,A_189)) ),
    inference(resolution,[status(thm)],[c_32,c_3386])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_275,plain,(
    ! [A_67,B_68,B_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | r1_tarski(k3_xboole_0(A_67,B_68),B_69) ) ),
    inference(resolution,[status(thm)],[c_8,c_102])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_515,plain,(
    ! [A_94,B_95,B_96] :
      ( k2_xboole_0(k3_xboole_0(A_94,B_95),B_96) = B_96
      | ~ r1_xboole_0(A_94,B_95) ) ),
    inference(resolution,[status(thm)],[c_275,c_38])).

tff(c_136,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_148,plain,(
    ! [A_55,B_56] : k2_xboole_0(k3_xboole_0(A_55,B_56),k4_xboole_0(A_55,B_56)) = k2_xboole_0(k3_xboole_0(A_55,B_56),A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_42])).

tff(c_153,plain,(
    ! [A_55,B_56] : k2_xboole_0(k3_xboole_0(A_55,B_56),k4_xboole_0(A_55,B_56)) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_148])).

tff(c_529,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = A_94
      | ~ r1_xboole_0(A_94,B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_153])).

tff(c_3471,plain,(
    ! [A_189,A_190] : k4_xboole_0(A_189,k4_xboole_0(A_190,A_189)) = A_189 ),
    inference(resolution,[status(thm)],[c_3438,c_529])).

tff(c_175,plain,(
    ! [A_61,B_62] : k4_xboole_0(k2_xboole_0(A_61,B_62),B_62) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_196,plain,(
    ! [A_28,B_29] : k4_xboole_0(k2_xboole_0(A_28,B_29),k4_xboole_0(B_29,A_28)) = k4_xboole_0(A_28,k4_xboole_0(B_29,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_175])).

tff(c_4682,plain,(
    ! [A_220,B_221] : k4_xboole_0(k2_xboole_0(A_220,B_221),k4_xboole_0(B_221,A_220)) = A_220 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3471,c_196])).

tff(c_4873,plain,(
    ! [A_32,B_33] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_32,B_33),A_32),k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4682])).

tff(c_4927,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2,c_4873])).

tff(c_48,plain,(
    k4_xboole_0('#skF_6',k4_xboole_0('#skF_6','#skF_7')) != k3_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4927,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:13:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.61/3.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.61/3.63  
% 10.61/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.61/3.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 10.61/3.64  
% 10.61/3.64  %Foreground sorts:
% 10.61/3.64  
% 10.61/3.64  
% 10.61/3.64  %Background operators:
% 10.61/3.64  
% 10.61/3.64  
% 10.61/3.64  %Foreground operators:
% 10.61/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.61/3.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.61/3.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.61/3.64  tff('#skF_7', type, '#skF_7': $i).
% 10.61/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.61/3.64  tff('#skF_6', type, '#skF_6': $i).
% 10.61/3.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.61/3.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.61/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.61/3.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.61/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.61/3.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.61/3.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.61/3.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.61/3.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.61/3.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.61/3.64  
% 10.61/3.65  tff(f_82, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 10.61/3.65  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.61/3.65  tff(f_88, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.61/3.65  tff(f_62, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.61/3.65  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.61/3.65  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.61/3.65  tff(f_76, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.61/3.65  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.61/3.65  tff(f_84, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.61/3.65  tff(f_86, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 10.61/3.65  tff(f_91, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.61/3.65  tff(c_40, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k3_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.61/3.65  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.61/3.65  tff(c_46, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.61/3.65  tff(c_32, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), A_14) | r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.61/3.65  tff(c_211, plain, (![A_63, B_64]: (r2_hidden('#skF_4'(A_63, B_64), B_64) | r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.61/3.65  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.61/3.65  tff(c_3386, plain, (![A_186, A_187, B_188]: (~r2_hidden('#skF_4'(A_186, k4_xboole_0(A_187, B_188)), B_188) | r1_xboole_0(A_186, k4_xboole_0(A_187, B_188)))), inference(resolution, [status(thm)], [c_211, c_12])).
% 10.61/3.65  tff(c_3438, plain, (![A_189, A_190]: (r1_xboole_0(A_189, k4_xboole_0(A_190, A_189)))), inference(resolution, [status(thm)], [c_32, c_3386])).
% 10.61/3.65  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.61/3.65  tff(c_102, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.61/3.65  tff(c_275, plain, (![A_67, B_68, B_69]: (~r1_xboole_0(A_67, B_68) | r1_tarski(k3_xboole_0(A_67, B_68), B_69))), inference(resolution, [status(thm)], [c_8, c_102])).
% 10.61/3.65  tff(c_38, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.61/3.65  tff(c_515, plain, (![A_94, B_95, B_96]: (k2_xboole_0(k3_xboole_0(A_94, B_95), B_96)=B_96 | ~r1_xboole_0(A_94, B_95))), inference(resolution, [status(thm)], [c_275, c_38])).
% 10.61/3.65  tff(c_136, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.61/3.65  tff(c_42, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.61/3.65  tff(c_148, plain, (![A_55, B_56]: (k2_xboole_0(k3_xboole_0(A_55, B_56), k4_xboole_0(A_55, B_56))=k2_xboole_0(k3_xboole_0(A_55, B_56), A_55))), inference(superposition, [status(thm), theory('equality')], [c_136, c_42])).
% 10.61/3.65  tff(c_153, plain, (![A_55, B_56]: (k2_xboole_0(k3_xboole_0(A_55, B_56), k4_xboole_0(A_55, B_56))=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_148])).
% 10.61/3.65  tff(c_529, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=A_94 | ~r1_xboole_0(A_94, B_95))), inference(superposition, [status(thm), theory('equality')], [c_515, c_153])).
% 10.61/3.65  tff(c_3471, plain, (![A_189, A_190]: (k4_xboole_0(A_189, k4_xboole_0(A_190, A_189))=A_189)), inference(resolution, [status(thm)], [c_3438, c_529])).
% 10.61/3.65  tff(c_175, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, B_62), B_62)=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.61/3.65  tff(c_196, plain, (![A_28, B_29]: (k4_xboole_0(k2_xboole_0(A_28, B_29), k4_xboole_0(B_29, A_28))=k4_xboole_0(A_28, k4_xboole_0(B_29, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_175])).
% 10.61/3.65  tff(c_4682, plain, (![A_220, B_221]: (k4_xboole_0(k2_xboole_0(A_220, B_221), k4_xboole_0(B_221, A_220))=A_220)), inference(demodulation, [status(thm), theory('equality')], [c_3471, c_196])).
% 10.61/3.65  tff(c_4873, plain, (![A_32, B_33]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_32, B_33), A_32), k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4682])).
% 10.61/3.65  tff(c_4927, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2, c_4873])).
% 10.61/3.65  tff(c_48, plain, (k4_xboole_0('#skF_6', k4_xboole_0('#skF_6', '#skF_7'))!=k3_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.61/3.65  tff(c_20440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4927, c_48])).
% 10.61/3.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.61/3.65  
% 10.61/3.65  Inference rules
% 10.61/3.65  ----------------------
% 10.61/3.65  #Ref     : 0
% 10.61/3.65  #Sup     : 5180
% 10.61/3.65  #Fact    : 0
% 10.61/3.65  #Define  : 0
% 10.61/3.65  #Split   : 0
% 10.61/3.65  #Chain   : 0
% 10.61/3.65  #Close   : 0
% 10.61/3.65  
% 10.61/3.65  Ordering : KBO
% 10.61/3.65  
% 10.61/3.65  Simplification rules
% 10.61/3.65  ----------------------
% 10.61/3.65  #Subsume      : 730
% 10.61/3.65  #Demod        : 4324
% 10.61/3.65  #Tautology    : 2281
% 10.61/3.65  #SimpNegUnit  : 75
% 10.61/3.65  #BackRed      : 6
% 10.61/3.65  
% 10.61/3.65  #Partial instantiations: 0
% 10.61/3.65  #Strategies tried      : 1
% 10.61/3.65  
% 10.61/3.65  Timing (in seconds)
% 10.61/3.65  ----------------------
% 10.61/3.65  Preprocessing        : 0.28
% 10.61/3.65  Parsing              : 0.15
% 10.61/3.65  CNF conversion       : 0.02
% 10.61/3.65  Main loop            : 2.68
% 10.61/3.65  Inferencing          : 0.63
% 10.61/3.65  Reduction            : 1.21
% 10.61/3.65  Demodulation         : 1.01
% 10.61/3.65  BG Simplification    : 0.08
% 10.61/3.65  Subsumption          : 0.59
% 10.61/3.65  Abstraction          : 0.12
% 10.61/3.65  MUC search           : 0.00
% 10.61/3.65  Cooper               : 0.00
% 10.61/3.66  Total                : 2.99
% 10.61/3.66  Index Insertion      : 0.00
% 10.61/3.66  Index Deletion       : 0.00
% 10.61/3.66  Index Matching       : 0.00
% 10.61/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
