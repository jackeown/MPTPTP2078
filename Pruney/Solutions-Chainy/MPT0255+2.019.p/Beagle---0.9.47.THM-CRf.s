%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:41 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 109 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 ( 120 expanded)
%              Number of equality atoms :   31 (  97 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
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

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_175,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(B_46,A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_40,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_248,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_40])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k1_xboole_0 = A_6
      | k2_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_135,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_42])).

tff(c_269,plain,(
    k2_xboole_0('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_135])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_269])).

tff(c_54,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_54])).

tff(c_350,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_61])).

tff(c_22,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_22])).

tff(c_346,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_139])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_473,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_733,plain,(
    ! [C_82,B_83,A_84] :
      ( ~ r2_hidden(C_82,B_83)
      | ~ r2_hidden(C_82,A_84)
      | k4_xboole_0(A_84,B_83) != A_84 ) ),
    inference(resolution,[status(thm)],[c_16,c_473])).

tff(c_752,plain,(
    ! [A_85] :
      ( ~ r2_hidden('#skF_5',A_85)
      | k4_xboole_0(A_85,'#skF_6') != A_85 ) ),
    inference(resolution,[status(thm)],[c_346,c_733])).

tff(c_755,plain,(
    k4_xboole_0('#skF_6','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_346,c_752])).

tff(c_767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.32  
% 2.11/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.32  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.52/1.32  
% 2.52/1.32  %Foreground sorts:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Background operators:
% 2.52/1.32  
% 2.52/1.32  
% 2.52/1.32  %Foreground operators:
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.52/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.52/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.52/1.32  
% 2.52/1.33  tff(f_49, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.52/1.33  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.52/1.33  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.52/1.33  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.52/1.33  tff(f_47, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.52/1.33  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.52/1.33  tff(f_66, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.52/1.33  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.52/1.33  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.52/1.33  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.52/1.33  tff(c_18, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.52/1.33  tff(c_175, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.52/1.33  tff(c_208, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(B_46, A_45))), inference(superposition, [status(thm), theory('equality')], [c_18, c_175])).
% 2.52/1.33  tff(c_40, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.52/1.33  tff(c_248, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_208, c_40])).
% 2.52/1.33  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.52/1.33  tff(c_8, plain, (![A_6, B_7]: (k1_xboole_0=A_6 | k2_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.33  tff(c_133, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_8])).
% 2.52/1.33  tff(c_135, plain, (k2_xboole_0(k1_xboole_0, '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_42])).
% 2.52/1.33  tff(c_269, plain, (k2_xboole_0('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_248, c_135])).
% 2.52/1.33  tff(c_329, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_269])).
% 2.52/1.33  tff(c_54, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(A_30, B_31))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.33  tff(c_61, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_54])).
% 2.52/1.33  tff(c_350, plain, (![A_8]: (k4_xboole_0(A_8, A_8)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_61])).
% 2.52/1.33  tff(c_22, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.52/1.33  tff(c_139, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_133, c_22])).
% 2.52/1.33  tff(c_346, plain, (r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_139])).
% 2.52/1.33  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.33  tff(c_473, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.33  tff(c_733, plain, (![C_82, B_83, A_84]: (~r2_hidden(C_82, B_83) | ~r2_hidden(C_82, A_84) | k4_xboole_0(A_84, B_83)!=A_84)), inference(resolution, [status(thm)], [c_16, c_473])).
% 2.52/1.33  tff(c_752, plain, (![A_85]: (~r2_hidden('#skF_5', A_85) | k4_xboole_0(A_85, '#skF_6')!=A_85)), inference(resolution, [status(thm)], [c_346, c_733])).
% 2.52/1.33  tff(c_755, plain, (k4_xboole_0('#skF_6', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_346, c_752])).
% 2.52/1.33  tff(c_767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_350, c_755])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 189
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 1
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 15
% 2.52/1.33  #Demod        : 83
% 2.52/1.33  #Tautology    : 139
% 2.52/1.33  #SimpNegUnit  : 0
% 2.52/1.33  #BackRed      : 14
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.33  Preprocessing        : 0.29
% 2.52/1.33  Parsing              : 0.15
% 2.52/1.33  CNF conversion       : 0.02
% 2.52/1.33  Main loop            : 0.28
% 2.52/1.33  Inferencing          : 0.10
% 2.52/1.33  Reduction            : 0.09
% 2.52/1.33  Demodulation         : 0.07
% 2.52/1.33  BG Simplification    : 0.02
% 2.52/1.33  Subsumption          : 0.05
% 2.52/1.33  Abstraction          : 0.02
% 2.52/1.33  MUC search           : 0.00
% 2.52/1.33  Cooper               : 0.00
% 2.52/1.33  Total                : 0.59
% 2.52/1.33  Index Insertion      : 0.00
% 2.52/1.33  Index Deletion       : 0.00
% 2.52/1.33  Index Matching       : 0.00
% 2.52/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
