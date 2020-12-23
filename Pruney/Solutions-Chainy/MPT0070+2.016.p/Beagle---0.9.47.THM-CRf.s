%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:20 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 224 expanded)
%              Number of leaves         :   26 (  86 expanded)
%              Depth                    :   25
%              Number of atoms          :   98 ( 346 expanded)
%              Number of equality atoms :   39 ( 141 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_63,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_42,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_160,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_168,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_160])).

tff(c_208,plain,(
    ! [A_44,B_45] : k2_xboole_0(k3_xboole_0(A_44,B_45),k4_xboole_0(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_220,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_208])).

tff(c_60,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_229,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_76])).

tff(c_312,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_339,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_312])).

tff(c_343,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_339])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_412,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,'#skF_5')
      | ~ r2_hidden(D_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_8])).

tff(c_1021,plain,(
    ! [B_89] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_89),'#skF_5')
      | r1_xboole_0(k1_xboole_0,B_89) ) ),
    inference(resolution,[status(thm)],[c_32,c_412])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_423,plain,(
    ! [D_59] :
      ( ~ r2_hidden(D_59,'#skF_5')
      | ~ r2_hidden(D_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_6])).

tff(c_432,plain,(
    ! [B_14] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_14),'#skF_5')
      | r1_xboole_0(k1_xboole_0,B_14) ) ),
    inference(resolution,[status(thm)],[c_32,c_423])).

tff(c_1033,plain,(
    ! [B_90] : r1_xboole_0(k1_xboole_0,B_90) ),
    inference(resolution,[status(thm)],[c_1021,c_432])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1045,plain,(
    ! [B_91] : r1_xboole_0(B_91,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1033,c_26])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1054,plain,(
    ! [B_91] : k3_xboole_0(B_91,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1045,c_22])).

tff(c_1091,plain,(
    ! [B_96] : k3_xboole_0(B_96,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1045,c_22])).

tff(c_40,plain,(
    ! [A_23,B_24] : k2_xboole_0(k3_xboole_0(A_23,B_24),k4_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1266,plain,(
    ! [B_108] : k2_xboole_0(k1_xboole_0,k4_xboole_0(B_108,k1_xboole_0)) = B_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_40])).

tff(c_1298,plain,(
    ! [B_109] : k4_xboole_0(B_109,k1_xboole_0) = B_109 ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_76])).

tff(c_38,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1311,plain,(
    ! [B_109] : k4_xboole_0(B_109,B_109) = k3_xboole_0(B_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1298,c_38])).

tff(c_1330,plain,(
    ! [B_109] : k4_xboole_0(B_109,B_109) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_1311])).

tff(c_46,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_149,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_153,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_149])).

tff(c_1502,plain,(
    ! [A_119,B_120] : k4_xboole_0(A_119,k3_xboole_0(A_119,B_120)) = k3_xboole_0(A_119,k4_xboole_0(A_119,B_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_38])).

tff(c_1552,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_1502])).

tff(c_1562,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1552])).

tff(c_173,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_189,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | k3_xboole_0(A_38,B_37) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_173,c_26])).

tff(c_198,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(B_37,A_38) = k1_xboole_0
      | k3_xboole_0(A_38,B_37) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_189,c_22])).

tff(c_1578,plain,(
    k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1562,c_198])).

tff(c_1592,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1578,c_40])).

tff(c_1602,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1592,c_76])).

tff(c_1639,plain,(
    ! [D_121] :
      ( ~ r2_hidden(D_121,'#skF_4')
      | ~ r2_hidden(D_121,k4_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_6])).

tff(c_1717,plain,(
    ! [D_124] :
      ( r2_hidden(D_124,'#skF_5')
      | ~ r2_hidden(D_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_1639])).

tff(c_244,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,'#skF_6')
      | ~ r2_hidden(D_8,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_6])).

tff(c_1743,plain,(
    ! [D_125] :
      ( ~ r2_hidden(D_125,'#skF_6')
      | ~ r2_hidden(D_125,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1717,c_244])).

tff(c_1777,plain,(
    ! [A_127] :
      ( ~ r2_hidden('#skF_3'(A_127,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_127,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_1743])).

tff(c_1781,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_1777])).

tff(c_1785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_1781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.54  
% 3.42/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.54  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.42/1.54  
% 3.42/1.54  %Foreground sorts:
% 3.42/1.54  
% 3.42/1.54  
% 3.42/1.54  %Background operators:
% 3.42/1.54  
% 3.42/1.54  
% 3.42/1.54  %Foreground operators:
% 3.42/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.42/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.54  
% 3.54/1.55  tff(f_80, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.54/1.55  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.54/1.55  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.54/1.55  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.54/1.55  tff(f_73, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.54/1.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.54/1.55  tff(f_65, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.54/1.55  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.54/1.55  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.54/1.55  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.54/1.55  tff(c_42, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.54/1.55  tff(c_32, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.54/1.55  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.54/1.55  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.55  tff(c_44, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.54/1.55  tff(c_160, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.55  tff(c_168, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_160])).
% 3.54/1.55  tff(c_208, plain, (![A_44, B_45]: (k2_xboole_0(k3_xboole_0(A_44, B_45), k4_xboole_0(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.54/1.55  tff(c_220, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_168, c_208])).
% 3.54/1.55  tff(c_60, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.55  tff(c_34, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.55  tff(c_76, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_60, c_34])).
% 3.54/1.55  tff(c_229, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_220, c_76])).
% 3.54/1.55  tff(c_312, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_339, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_229, c_312])).
% 3.54/1.55  tff(c_343, plain, (k4_xboole_0('#skF_5', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_168, c_339])).
% 3.54/1.55  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.55  tff(c_412, plain, (![D_58]: (r2_hidden(D_58, '#skF_5') | ~r2_hidden(D_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_343, c_8])).
% 3.54/1.55  tff(c_1021, plain, (![B_89]: (r2_hidden('#skF_3'(k1_xboole_0, B_89), '#skF_5') | r1_xboole_0(k1_xboole_0, B_89))), inference(resolution, [status(thm)], [c_32, c_412])).
% 3.54/1.55  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.55  tff(c_423, plain, (![D_59]: (~r2_hidden(D_59, '#skF_5') | ~r2_hidden(D_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_343, c_6])).
% 3.54/1.55  tff(c_432, plain, (![B_14]: (~r2_hidden('#skF_3'(k1_xboole_0, B_14), '#skF_5') | r1_xboole_0(k1_xboole_0, B_14))), inference(resolution, [status(thm)], [c_32, c_423])).
% 3.54/1.55  tff(c_1033, plain, (![B_90]: (r1_xboole_0(k1_xboole_0, B_90))), inference(resolution, [status(thm)], [c_1021, c_432])).
% 3.54/1.55  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.54/1.55  tff(c_1045, plain, (![B_91]: (r1_xboole_0(B_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_1033, c_26])).
% 3.54/1.55  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.55  tff(c_1054, plain, (![B_91]: (k3_xboole_0(B_91, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1045, c_22])).
% 3.54/1.55  tff(c_1091, plain, (![B_96]: (k3_xboole_0(B_96, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1045, c_22])).
% 3.54/1.55  tff(c_40, plain, (![A_23, B_24]: (k2_xboole_0(k3_xboole_0(A_23, B_24), k4_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.54/1.55  tff(c_1266, plain, (![B_108]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_108, k1_xboole_0))=B_108)), inference(superposition, [status(thm), theory('equality')], [c_1091, c_40])).
% 3.54/1.55  tff(c_1298, plain, (![B_109]: (k4_xboole_0(B_109, k1_xboole_0)=B_109)), inference(superposition, [status(thm), theory('equality')], [c_1266, c_76])).
% 3.54/1.55  tff(c_38, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_1311, plain, (![B_109]: (k4_xboole_0(B_109, B_109)=k3_xboole_0(B_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1298, c_38])).
% 3.54/1.55  tff(c_1330, plain, (![B_109]: (k4_xboole_0(B_109, B_109)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_1311])).
% 3.54/1.55  tff(c_46, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.54/1.55  tff(c_149, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.54/1.55  tff(c_153, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_149])).
% 3.54/1.55  tff(c_1502, plain, (![A_119, B_120]: (k4_xboole_0(A_119, k3_xboole_0(A_119, B_120))=k3_xboole_0(A_119, k4_xboole_0(A_119, B_120)))), inference(superposition, [status(thm), theory('equality')], [c_312, c_38])).
% 3.54/1.55  tff(c_1552, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_153, c_1502])).
% 3.54/1.55  tff(c_1562, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1552])).
% 3.54/1.55  tff(c_173, plain, (![A_35, B_36]: (r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.55  tff(c_189, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | k3_xboole_0(A_38, B_37)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_173, c_26])).
% 3.54/1.55  tff(c_198, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k1_xboole_0 | k3_xboole_0(A_38, B_37)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_189, c_22])).
% 3.54/1.55  tff(c_1578, plain, (k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1562, c_198])).
% 3.54/1.55  tff(c_1592, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1578, c_40])).
% 3.54/1.55  tff(c_1602, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1592, c_76])).
% 3.54/1.55  tff(c_1639, plain, (![D_121]: (~r2_hidden(D_121, '#skF_4') | ~r2_hidden(D_121, k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1602, c_6])).
% 3.54/1.55  tff(c_1717, plain, (![D_124]: (r2_hidden(D_124, '#skF_5') | ~r2_hidden(D_124, '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_1639])).
% 3.54/1.55  tff(c_244, plain, (![D_8]: (~r2_hidden(D_8, '#skF_6') | ~r2_hidden(D_8, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_6])).
% 3.54/1.55  tff(c_1743, plain, (![D_125]: (~r2_hidden(D_125, '#skF_6') | ~r2_hidden(D_125, '#skF_4'))), inference(resolution, [status(thm)], [c_1717, c_244])).
% 3.54/1.55  tff(c_1777, plain, (![A_127]: (~r2_hidden('#skF_3'(A_127, '#skF_6'), '#skF_4') | r1_xboole_0(A_127, '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_1743])).
% 3.54/1.55  tff(c_1781, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_32, c_1777])).
% 3.54/1.55  tff(c_1785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_1781])).
% 3.54/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.55  
% 3.54/1.55  Inference rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Ref     : 0
% 3.54/1.55  #Sup     : 435
% 3.54/1.55  #Fact    : 0
% 3.54/1.55  #Define  : 0
% 3.54/1.55  #Split   : 2
% 3.54/1.55  #Chain   : 0
% 3.54/1.55  #Close   : 0
% 3.54/1.55  
% 3.54/1.55  Ordering : KBO
% 3.54/1.55  
% 3.54/1.55  Simplification rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Subsume      : 39
% 3.54/1.55  #Demod        : 221
% 3.54/1.55  #Tautology    : 273
% 3.54/1.55  #SimpNegUnit  : 1
% 3.54/1.55  #BackRed      : 10
% 3.54/1.55  
% 3.54/1.55  #Partial instantiations: 0
% 3.54/1.55  #Strategies tried      : 1
% 3.54/1.55  
% 3.54/1.55  Timing (in seconds)
% 3.54/1.55  ----------------------
% 3.54/1.56  Preprocessing        : 0.29
% 3.54/1.56  Parsing              : 0.16
% 3.54/1.56  CNF conversion       : 0.02
% 3.54/1.56  Main loop            : 0.50
% 3.54/1.56  Inferencing          : 0.18
% 3.54/1.56  Reduction            : 0.16
% 3.54/1.56  Demodulation         : 0.12
% 3.54/1.56  BG Simplification    : 0.02
% 3.54/1.56  Subsumption          : 0.10
% 3.54/1.56  Abstraction          : 0.02
% 3.54/1.56  MUC search           : 0.00
% 3.54/1.56  Cooper               : 0.00
% 3.54/1.56  Total                : 0.83
% 3.54/1.56  Index Insertion      : 0.00
% 3.54/1.56  Index Deletion       : 0.00
% 3.54/1.56  Index Matching       : 0.00
% 3.54/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
