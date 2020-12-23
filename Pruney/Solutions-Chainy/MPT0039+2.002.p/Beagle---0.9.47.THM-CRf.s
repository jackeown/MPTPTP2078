%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:42 EST 2020

% Result     : Theorem 8.34s
% Output     : CNFRefutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 283 expanded)
%              Number of leaves         :   15 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 754 expanded)
%              Number of equality atoms :   33 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_40,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1334,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r2_hidden('#skF_1'(A_101,B_102,C_103),C_103)
      | r2_hidden('#skF_2'(A_101,B_102,C_103),C_103)
      | k3_xboole_0(A_101,B_102) = C_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1355,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,B_4),B_4)
      | k3_xboole_0(A_3,B_4) = B_4 ) ),
    inference(resolution,[status(thm)],[c_18,c_1334])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2854,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_hidden('#skF_1'(A_145,B_146,C_147),A_145)
      | ~ r2_hidden('#skF_2'(A_145,B_146,C_147),B_146)
      | ~ r2_hidden('#skF_2'(A_145,B_146,C_147),A_145)
      | k3_xboole_0(A_145,B_146) = C_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3456,plain,(
    ! [A_164,C_165] :
      ( ~ r2_hidden('#skF_2'(A_164,C_165,C_165),A_164)
      | r2_hidden('#skF_1'(A_164,C_165,C_165),A_164)
      | k3_xboole_0(A_164,C_165) = C_165 ) ),
    inference(resolution,[status(thm)],[c_20,c_2854])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3529,plain,(
    ! [A_166] :
      ( ~ r2_hidden('#skF_2'(A_166,A_166,A_166),A_166)
      | k3_xboole_0(A_166,A_166) = A_166 ) ),
    inference(resolution,[status(thm)],[c_3456,c_10])).

tff(c_3558,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_1355,c_3529])).

tff(c_119,plain,(
    ! [D_34,A_35,B_36] :
      ( r2_hidden(D_34,k4_xboole_0(A_35,B_36))
      | r2_hidden(D_34,B_36)
      | ~ r2_hidden(D_34,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k4_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [D_26,B_27,A_28] :
      ( ~ r2_hidden(D_26,B_27)
      | ~ r2_hidden(D_26,k4_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_101,plain,(
    ! [D_26] :
      ( ~ r2_hidden(D_26,'#skF_6')
      | ~ r2_hidden(D_26,k4_xboole_0('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_98])).

tff(c_137,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,'#skF_5')
      | ~ r2_hidden(D_34,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_119,c_101])).

tff(c_8321,plain,(
    ! [A_299,B_300] :
      ( r2_hidden('#skF_2'(A_299,B_300,'#skF_5'),'#skF_5')
      | k3_xboole_0(A_299,B_300) = '#skF_5'
      | ~ r2_hidden('#skF_1'(A_299,B_300,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_137,c_1334])).

tff(c_8375,plain,(
    ! [B_302] :
      ( r2_hidden('#skF_2'('#skF_6',B_302,'#skF_5'),'#skF_5')
      | k3_xboole_0('#skF_6',B_302) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_20,c_8321])).

tff(c_155,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,k4_xboole_0('#skF_6','#skF_5'))
      | r2_hidden(D_41,'#skF_6')
      | ~ r2_hidden(D_41,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_119])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_174,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_6')
      | ~ r2_hidden(D_41,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_155,c_24])).

tff(c_8389,plain,(
    ! [B_302] :
      ( r2_hidden('#skF_2'('#skF_6',B_302,'#skF_5'),'#skF_6')
      | k3_xboole_0('#skF_6',B_302) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_8375,c_174])).

tff(c_8359,plain,(
    ! [A_301] :
      ( r2_hidden('#skF_2'(A_301,'#skF_6','#skF_5'),'#skF_5')
      | k3_xboole_0(A_301,'#skF_6') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_18,c_8321])).

tff(c_8390,plain,(
    ! [A_303] :
      ( r2_hidden('#skF_2'(A_303,'#skF_6','#skF_5'),'#skF_6')
      | k3_xboole_0(A_303,'#skF_6') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_8359,c_174])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8395,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_6','#skF_5'),'#skF_6')
    | k3_xboole_0('#skF_6','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8390,c_12])).

tff(c_8402,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_6','#skF_5'),'#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_8395])).

tff(c_8403,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_6','#skF_6','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_8402])).

tff(c_8533,plain,(
    ~ r2_hidden('#skF_2'('#skF_6','#skF_6','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_8403])).

tff(c_8536,plain,(
    k3_xboole_0('#skF_6','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8389,c_8533])).

tff(c_8541,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_8536])).

tff(c_8543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_8541])).

tff(c_8545,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_6','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_8403])).

tff(c_8544,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_8403])).

tff(c_22,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,k4_xboole_0(A_9,B_10))
      | r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_181,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden('#skF_3'(A_43,B_44,C_45),A_43)
      | r2_hidden('#skF_4'(A_43,B_44,C_45),C_45)
      | k4_xboole_0(A_43,B_44) = C_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),B_10)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_253,plain,(
    ! [A_46,C_47] :
      ( r2_hidden('#skF_4'(A_46,A_46,C_47),C_47)
      | k4_xboole_0(A_46,A_46) = C_47 ) ),
    inference(resolution,[status(thm)],[c_181,c_36])).

tff(c_26,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_288,plain,(
    ! [A_46,A_9,B_10] :
      ( r2_hidden('#skF_4'(A_46,A_46,k4_xboole_0(A_9,B_10)),A_9)
      | k4_xboole_0(A_9,B_10) = k4_xboole_0(A_46,A_46) ) ),
    inference(resolution,[status(thm)],[c_253,c_26])).

tff(c_440,plain,(
    ! [A_58] :
      ( ~ r2_hidden('#skF_4'(A_58,A_58,k4_xboole_0('#skF_6','#skF_5')),'#skF_6')
      | k4_xboole_0(A_58,A_58) = k4_xboole_0('#skF_6','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_253,c_101])).

tff(c_446,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k4_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_288,c_440])).

tff(c_469,plain,(
    ! [D_14,A_59] :
      ( ~ r2_hidden(D_14,A_59)
      | ~ r2_hidden(D_14,k4_xboole_0('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_24])).

tff(c_8557,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),k4_xboole_0('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_8544,c_469])).

tff(c_8935,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_8557])).

tff(c_8938,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_6','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_8935])).

tff(c_8940,plain,
    ( ~ r2_hidden('#skF_2'('#skF_6','#skF_6','#skF_5'),'#skF_6')
    | k3_xboole_0('#skF_6','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8938,c_10])).

tff(c_8953,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3558,c_8545,c_8940])).

tff(c_8955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_8953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.34/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/2.81  
% 8.34/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/2.81  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 8.34/2.81  
% 8.34/2.81  %Foreground sorts:
% 8.34/2.81  
% 8.34/2.81  
% 8.34/2.81  %Background operators:
% 8.34/2.81  
% 8.34/2.81  
% 8.34/2.81  %Foreground operators:
% 8.34/2.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.34/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.34/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.34/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.34/2.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.34/2.81  tff('#skF_5', type, '#skF_5': $i).
% 8.34/2.81  tff('#skF_6', type, '#skF_6': $i).
% 8.34/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.34/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.34/2.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.34/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.34/2.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.34/2.81  
% 8.34/2.82  tff(f_51, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 8.34/2.82  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.34/2.82  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.34/2.82  tff(c_40, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.34/2.82  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.34/2.82  tff(c_1334, plain, (![A_101, B_102, C_103]: (~r2_hidden('#skF_1'(A_101, B_102, C_103), C_103) | r2_hidden('#skF_2'(A_101, B_102, C_103), C_103) | k3_xboole_0(A_101, B_102)=C_103)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.34/2.82  tff(c_1355, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, B_4), B_4) | k3_xboole_0(A_3, B_4)=B_4)), inference(resolution, [status(thm)], [c_18, c_1334])).
% 8.34/2.82  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.34/2.82  tff(c_2854, plain, (![A_145, B_146, C_147]: (r2_hidden('#skF_1'(A_145, B_146, C_147), A_145) | ~r2_hidden('#skF_2'(A_145, B_146, C_147), B_146) | ~r2_hidden('#skF_2'(A_145, B_146, C_147), A_145) | k3_xboole_0(A_145, B_146)=C_147)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.34/2.82  tff(c_3456, plain, (![A_164, C_165]: (~r2_hidden('#skF_2'(A_164, C_165, C_165), A_164) | r2_hidden('#skF_1'(A_164, C_165, C_165), A_164) | k3_xboole_0(A_164, C_165)=C_165)), inference(resolution, [status(thm)], [c_20, c_2854])).
% 8.34/2.82  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.34/2.82  tff(c_3529, plain, (![A_166]: (~r2_hidden('#skF_2'(A_166, A_166, A_166), A_166) | k3_xboole_0(A_166, A_166)=A_166)), inference(resolution, [status(thm)], [c_3456, c_10])).
% 8.34/2.82  tff(c_3558, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_1355, c_3529])).
% 8.34/2.82  tff(c_119, plain, (![D_34, A_35, B_36]: (r2_hidden(D_34, k4_xboole_0(A_35, B_36)) | r2_hidden(D_34, B_36) | ~r2_hidden(D_34, A_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.34/2.82  tff(c_42, plain, (k4_xboole_0('#skF_5', '#skF_6')=k4_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.34/2.82  tff(c_98, plain, (![D_26, B_27, A_28]: (~r2_hidden(D_26, B_27) | ~r2_hidden(D_26, k4_xboole_0(A_28, B_27)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.34/2.82  tff(c_101, plain, (![D_26]: (~r2_hidden(D_26, '#skF_6') | ~r2_hidden(D_26, k4_xboole_0('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_98])).
% 8.34/2.82  tff(c_137, plain, (![D_34]: (r2_hidden(D_34, '#skF_5') | ~r2_hidden(D_34, '#skF_6'))), inference(resolution, [status(thm)], [c_119, c_101])).
% 8.34/2.82  tff(c_8321, plain, (![A_299, B_300]: (r2_hidden('#skF_2'(A_299, B_300, '#skF_5'), '#skF_5') | k3_xboole_0(A_299, B_300)='#skF_5' | ~r2_hidden('#skF_1'(A_299, B_300, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_137, c_1334])).
% 8.34/2.82  tff(c_8375, plain, (![B_302]: (r2_hidden('#skF_2'('#skF_6', B_302, '#skF_5'), '#skF_5') | k3_xboole_0('#skF_6', B_302)='#skF_5')), inference(resolution, [status(thm)], [c_20, c_8321])).
% 8.34/2.82  tff(c_155, plain, (![D_41]: (r2_hidden(D_41, k4_xboole_0('#skF_6', '#skF_5')) | r2_hidden(D_41, '#skF_6') | ~r2_hidden(D_41, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_119])).
% 8.34/2.82  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.34/2.82  tff(c_174, plain, (![D_41]: (r2_hidden(D_41, '#skF_6') | ~r2_hidden(D_41, '#skF_5'))), inference(resolution, [status(thm)], [c_155, c_24])).
% 8.34/2.82  tff(c_8389, plain, (![B_302]: (r2_hidden('#skF_2'('#skF_6', B_302, '#skF_5'), '#skF_6') | k3_xboole_0('#skF_6', B_302)='#skF_5')), inference(resolution, [status(thm)], [c_8375, c_174])).
% 8.34/2.82  tff(c_8359, plain, (![A_301]: (r2_hidden('#skF_2'(A_301, '#skF_6', '#skF_5'), '#skF_5') | k3_xboole_0(A_301, '#skF_6')='#skF_5')), inference(resolution, [status(thm)], [c_18, c_8321])).
% 8.34/2.82  tff(c_8390, plain, (![A_303]: (r2_hidden('#skF_2'(A_303, '#skF_6', '#skF_5'), '#skF_6') | k3_xboole_0(A_303, '#skF_6')='#skF_5')), inference(resolution, [status(thm)], [c_8359, c_174])).
% 8.34/2.82  tff(c_12, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.34/2.82  tff(c_8395, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_6', '#skF_6', '#skF_5'), '#skF_6') | k3_xboole_0('#skF_6', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_8390, c_12])).
% 8.34/2.82  tff(c_8402, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_6', '#skF_6', '#skF_5'), '#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_8395])).
% 8.34/2.82  tff(c_8403, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_6', '#skF_6', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_40, c_8402])).
% 8.34/2.82  tff(c_8533, plain, (~r2_hidden('#skF_2'('#skF_6', '#skF_6', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_8403])).
% 8.34/2.82  tff(c_8536, plain, (k3_xboole_0('#skF_6', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_8389, c_8533])).
% 8.34/2.82  tff(c_8541, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_8536])).
% 8.34/2.82  tff(c_8543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_8541])).
% 8.34/2.82  tff(c_8545, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_6', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_8403])).
% 8.34/2.82  tff(c_8544, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_8403])).
% 8.34/2.82  tff(c_22, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, k4_xboole_0(A_9, B_10)) | r2_hidden(D_14, B_10) | ~r2_hidden(D_14, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.34/2.82  tff(c_181, plain, (![A_43, B_44, C_45]: (r2_hidden('#skF_3'(A_43, B_44, C_45), A_43) | r2_hidden('#skF_4'(A_43, B_44, C_45), C_45) | k4_xboole_0(A_43, B_44)=C_45)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.34/2.82  tff(c_36, plain, (![A_9, B_10, C_11]: (~r2_hidden('#skF_3'(A_9, B_10, C_11), B_10) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.34/2.82  tff(c_253, plain, (![A_46, C_47]: (r2_hidden('#skF_4'(A_46, A_46, C_47), C_47) | k4_xboole_0(A_46, A_46)=C_47)), inference(resolution, [status(thm)], [c_181, c_36])).
% 8.34/2.82  tff(c_26, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, A_9) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.34/2.82  tff(c_288, plain, (![A_46, A_9, B_10]: (r2_hidden('#skF_4'(A_46, A_46, k4_xboole_0(A_9, B_10)), A_9) | k4_xboole_0(A_9, B_10)=k4_xboole_0(A_46, A_46))), inference(resolution, [status(thm)], [c_253, c_26])).
% 8.34/2.82  tff(c_440, plain, (![A_58]: (~r2_hidden('#skF_4'(A_58, A_58, k4_xboole_0('#skF_6', '#skF_5')), '#skF_6') | k4_xboole_0(A_58, A_58)=k4_xboole_0('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_253, c_101])).
% 8.34/2.82  tff(c_446, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k4_xboole_0('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_288, c_440])).
% 8.34/2.82  tff(c_469, plain, (![D_14, A_59]: (~r2_hidden(D_14, A_59) | ~r2_hidden(D_14, k4_xboole_0('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_446, c_24])).
% 8.34/2.82  tff(c_8557, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), k4_xboole_0('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_8544, c_469])).
% 8.34/2.82  tff(c_8935, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_22, c_8557])).
% 8.34/2.82  tff(c_8938, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_6', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_8935])).
% 8.34/2.82  tff(c_8940, plain, (~r2_hidden('#skF_2'('#skF_6', '#skF_6', '#skF_5'), '#skF_6') | k3_xboole_0('#skF_6', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_8938, c_10])).
% 8.34/2.82  tff(c_8953, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3558, c_8545, c_8940])).
% 8.34/2.82  tff(c_8955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_8953])).
% 8.34/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/2.82  
% 8.34/2.82  Inference rules
% 8.34/2.82  ----------------------
% 8.34/2.82  #Ref     : 0
% 8.34/2.82  #Sup     : 2212
% 8.34/2.82  #Fact    : 0
% 8.34/2.82  #Define  : 0
% 8.34/2.82  #Split   : 2
% 8.34/2.82  #Chain   : 0
% 8.34/2.82  #Close   : 0
% 8.34/2.82  
% 8.34/2.82  Ordering : KBO
% 8.34/2.82  
% 8.34/2.82  Simplification rules
% 8.34/2.82  ----------------------
% 8.34/2.82  #Subsume      : 705
% 8.34/2.82  #Demod        : 1603
% 8.34/2.82  #Tautology    : 405
% 8.34/2.82  #SimpNegUnit  : 26
% 8.34/2.82  #BackRed      : 51
% 8.34/2.82  
% 8.34/2.82  #Partial instantiations: 0
% 8.34/2.82  #Strategies tried      : 1
% 8.34/2.82  
% 8.34/2.82  Timing (in seconds)
% 8.34/2.82  ----------------------
% 8.34/2.83  Preprocessing        : 0.27
% 8.34/2.83  Parsing              : 0.13
% 8.34/2.83  CNF conversion       : 0.02
% 8.34/2.83  Main loop            : 1.75
% 8.34/2.83  Inferencing          : 0.46
% 8.34/2.83  Reduction            : 0.70
% 8.34/2.83  Demodulation         : 0.57
% 8.34/2.83  BG Simplification    : 0.06
% 8.34/2.83  Subsumption          : 0.39
% 8.34/2.83  Abstraction          : 0.08
% 8.34/2.83  MUC search           : 0.00
% 8.34/2.83  Cooper               : 0.00
% 8.34/2.83  Total                : 2.05
% 8.34/2.83  Index Insertion      : 0.00
% 8.34/2.83  Index Deletion       : 0.00
% 8.34/2.83  Index Matching       : 0.00
% 8.34/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
