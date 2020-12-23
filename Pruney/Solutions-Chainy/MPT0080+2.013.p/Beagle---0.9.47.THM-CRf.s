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
% DateTime   : Thu Dec  3 09:43:51 EST 2020

% Result     : Theorem 16.79s
% Output     : CNFRefutation 16.79s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 285 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :   87 ( 496 expanded)
%              Number of equality atoms :   41 ( 152 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_64,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_32])).

tff(c_246,plain,(
    ! [A_46,B_47] : k2_xboole_0(A_46,k4_xboole_0(B_47,A_46)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_256,plain,(
    ! [B_47] : k4_xboole_0(B_47,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_86])).

tff(c_268,plain,(
    ! [B_47] : k4_xboole_0(B_47,k1_xboole_0) = B_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_256])).

tff(c_892,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16221,plain,(
    ! [A_324,B_325,B_326] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_324,B_325),B_326),A_324)
      | r1_tarski(k4_xboole_0(A_324,B_325),B_326) ) ),
    inference(resolution,[status(thm)],[c_892,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16407,plain,(
    ! [A_324,B_325] : r1_tarski(k4_xboole_0(A_324,B_325),A_324) ),
    inference(resolution,[status(thm)],[c_16221,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_49,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_186,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_205,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_49,c_186])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_907,plain,(
    ! [A_8,B_9,B_75] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_8,B_9),B_75),B_9)
      | r1_tarski(k4_xboole_0(A_8,B_9),B_75) ) ),
    inference(resolution,[status(thm)],[c_892,c_12])).

tff(c_16380,plain,(
    ! [A_324,B_326] : r1_tarski(k4_xboole_0(A_324,A_324),B_326) ),
    inference(resolution,[status(thm)],[c_16221,c_907])).

tff(c_16443,plain,(
    ! [A_327,B_328] : r1_tarski(k4_xboole_0(A_327,A_327),B_328) ),
    inference(resolution,[status(thm)],[c_16221,c_907])).

tff(c_46,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2692,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_xboole_0 = A_117
      | ~ r1_xboole_0(B_118,C_119)
      | ~ r1_tarski(A_117,C_119)
      | ~ r1_tarski(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2698,plain,(
    ! [A_117] :
      ( k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,'#skF_6')
      | ~ r1_tarski(A_117,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_2692])).

tff(c_16450,plain,(
    ! [A_327] :
      ( k4_xboole_0(A_327,A_327) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_327,A_327),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16443,c_2698])).

tff(c_16476,plain,(
    ! [A_327] : k4_xboole_0(A_327,A_327) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16380,c_16450])).

tff(c_349,plain,(
    ! [A_53,B_54] : k4_xboole_0(k2_xboole_0(A_53,B_54),B_54) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_381,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k4_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_349])).

tff(c_16508,plain,(
    ! [A_36] : k4_xboole_0(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16476,c_381])).

tff(c_16517,plain,(
    ! [A_329] : k4_xboole_0(A_329,A_329) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16380,c_16450])).

tff(c_38,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k4_xboole_0(A_23,B_24),C_25) = k4_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16620,plain,(
    ! [A_329,C_25] : k4_xboole_0(A_329,k2_xboole_0(A_329,C_25)) = k4_xboole_0(k1_xboole_0,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_16517,c_38])).

tff(c_17784,plain,(
    ! [A_347,C_348] : k4_xboole_0(A_347,k2_xboole_0(A_347,C_348)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16508,c_16620])).

tff(c_17923,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_17784])).

tff(c_1624,plain,(
    ! [A_94,B_95,C_96] : k4_xboole_0(k4_xboole_0(A_94,B_95),C_96) = k4_xboole_0(A_94,k2_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14140,plain,(
    ! [C_310,A_311,B_312] : k2_xboole_0(C_310,k4_xboole_0(A_311,k2_xboole_0(B_312,C_310))) = k2_xboole_0(C_310,k4_xboole_0(A_311,B_312)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_34])).

tff(c_54817,plain,(
    ! [A_683,A_684,B_685] : k2_xboole_0(A_683,k4_xboole_0(A_684,k2_xboole_0(A_683,B_685))) = k2_xboole_0(A_683,k4_xboole_0(A_684,B_685)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14140])).

tff(c_55408,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_17923,c_54817])).

tff(c_55658,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_55408])).

tff(c_42,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,(
    ! [A_36,B_35] : r1_tarski(A_36,k2_xboole_0(B_35,A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_55989,plain,(
    r1_tarski(k4_xboole_0('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_55658,c_79])).

tff(c_56073,plain,
    ( k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_55989,c_2698])).

tff(c_56080,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16407,c_56073])).

tff(c_15378,plain,(
    ! [A_322,B_323] : k4_xboole_0(k2_xboole_0(A_322,B_323),k4_xboole_0(B_323,A_322)) = k4_xboole_0(A_322,k4_xboole_0(B_323,A_322)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_349])).

tff(c_15588,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_15378])).

tff(c_56114,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),k1_xboole_0) = k4_xboole_0('#skF_5',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56080,c_15588])).

tff(c_56313,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_56080,c_268,c_56114])).

tff(c_56776,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_56313,c_42])).

tff(c_56845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_56776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n001.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 20:57:00 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.79/9.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.79/9.15  
% 16.79/9.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.79/9.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 16.79/9.15  
% 16.79/9.15  %Foreground sorts:
% 16.79/9.15  
% 16.79/9.15  
% 16.79/9.15  %Background operators:
% 16.79/9.15  
% 16.79/9.15  
% 16.79/9.15  %Foreground operators:
% 16.79/9.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.79/9.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.79/9.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.79/9.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.79/9.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.79/9.15  tff('#skF_5', type, '#skF_5': $i).
% 16.79/9.15  tff('#skF_6', type, '#skF_6': $i).
% 16.79/9.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.79/9.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.79/9.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.79/9.15  tff('#skF_4', type, '#skF_4': $i).
% 16.79/9.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.79/9.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.79/9.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.79/9.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.79/9.15  
% 16.79/9.16  tff(f_77, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 16.79/9.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.79/9.16  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 16.79/9.16  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 16.79/9.16  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.79/9.16  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.79/9.16  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.79/9.16  tff(f_68, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 16.79/9.16  tff(f_58, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 16.79/9.16  tff(f_60, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 16.79/9.16  tff(f_70, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.79/9.16  tff(c_44, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.79/9.16  tff(c_64, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.79/9.16  tff(c_32, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.79/9.16  tff(c_86, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_64, c_32])).
% 16.79/9.16  tff(c_246, plain, (![A_46, B_47]: (k2_xboole_0(A_46, k4_xboole_0(B_47, A_46))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.79/9.16  tff(c_256, plain, (![B_47]: (k4_xboole_0(B_47, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_47))), inference(superposition, [status(thm), theory('equality')], [c_246, c_86])).
% 16.79/9.16  tff(c_268, plain, (![B_47]: (k4_xboole_0(B_47, k1_xboole_0)=B_47)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_256])).
% 16.79/9.16  tff(c_892, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.79/9.16  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.79/9.16  tff(c_16221, plain, (![A_324, B_325, B_326]: (r2_hidden('#skF_1'(k4_xboole_0(A_324, B_325), B_326), A_324) | r1_tarski(k4_xboole_0(A_324, B_325), B_326))), inference(resolution, [status(thm)], [c_892, c_14])).
% 16.79/9.16  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.79/9.16  tff(c_16407, plain, (![A_324, B_325]: (r1_tarski(k4_xboole_0(A_324, B_325), A_324))), inference(resolution, [status(thm)], [c_16221, c_6])).
% 16.79/9.16  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.79/9.16  tff(c_48, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.79/9.16  tff(c_49, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 16.79/9.16  tff(c_186, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.79/9.16  tff(c_205, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_49, c_186])).
% 16.79/9.16  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.79/9.16  tff(c_907, plain, (![A_8, B_9, B_75]: (~r2_hidden('#skF_1'(k4_xboole_0(A_8, B_9), B_75), B_9) | r1_tarski(k4_xboole_0(A_8, B_9), B_75))), inference(resolution, [status(thm)], [c_892, c_12])).
% 16.79/9.16  tff(c_16380, plain, (![A_324, B_326]: (r1_tarski(k4_xboole_0(A_324, A_324), B_326))), inference(resolution, [status(thm)], [c_16221, c_907])).
% 16.79/9.16  tff(c_16443, plain, (![A_327, B_328]: (r1_tarski(k4_xboole_0(A_327, A_327), B_328))), inference(resolution, [status(thm)], [c_16221, c_907])).
% 16.79/9.16  tff(c_46, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.79/9.16  tff(c_2692, plain, (![A_117, B_118, C_119]: (k1_xboole_0=A_117 | ~r1_xboole_0(B_118, C_119) | ~r1_tarski(A_117, C_119) | ~r1_tarski(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.79/9.16  tff(c_2698, plain, (![A_117]: (k1_xboole_0=A_117 | ~r1_tarski(A_117, '#skF_6') | ~r1_tarski(A_117, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_2692])).
% 16.79/9.16  tff(c_16450, plain, (![A_327]: (k4_xboole_0(A_327, A_327)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_327, A_327), '#skF_4'))), inference(resolution, [status(thm)], [c_16443, c_2698])).
% 16.79/9.16  tff(c_16476, plain, (![A_327]: (k4_xboole_0(A_327, A_327)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16380, c_16450])).
% 16.79/9.16  tff(c_349, plain, (![A_53, B_54]: (k4_xboole_0(k2_xboole_0(A_53, B_54), B_54)=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.79/9.16  tff(c_381, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k4_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_86, c_349])).
% 16.79/9.16  tff(c_16508, plain, (![A_36]: (k4_xboole_0(k1_xboole_0, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16476, c_381])).
% 16.79/9.16  tff(c_16517, plain, (![A_329]: (k4_xboole_0(A_329, A_329)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16380, c_16450])).
% 16.79/9.16  tff(c_38, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k4_xboole_0(A_23, B_24), C_25)=k4_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.79/9.16  tff(c_16620, plain, (![A_329, C_25]: (k4_xboole_0(A_329, k2_xboole_0(A_329, C_25))=k4_xboole_0(k1_xboole_0, C_25))), inference(superposition, [status(thm), theory('equality')], [c_16517, c_38])).
% 16.79/9.16  tff(c_17784, plain, (![A_347, C_348]: (k4_xboole_0(A_347, k2_xboole_0(A_347, C_348))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16508, c_16620])).
% 16.79/9.16  tff(c_17923, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_205, c_17784])).
% 16.79/9.16  tff(c_1624, plain, (![A_94, B_95, C_96]: (k4_xboole_0(k4_xboole_0(A_94, B_95), C_96)=k4_xboole_0(A_94, k2_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.79/9.16  tff(c_34, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.79/9.16  tff(c_14140, plain, (![C_310, A_311, B_312]: (k2_xboole_0(C_310, k4_xboole_0(A_311, k2_xboole_0(B_312, C_310)))=k2_xboole_0(C_310, k4_xboole_0(A_311, B_312)))), inference(superposition, [status(thm), theory('equality')], [c_1624, c_34])).
% 16.79/9.16  tff(c_54817, plain, (![A_683, A_684, B_685]: (k2_xboole_0(A_683, k4_xboole_0(A_684, k2_xboole_0(A_683, B_685)))=k2_xboole_0(A_683, k4_xboole_0(A_684, B_685)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14140])).
% 16.79/9.16  tff(c_55408, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17923, c_54817])).
% 16.79/9.16  tff(c_55658, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_55408])).
% 16.79/9.16  tff(c_42, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.79/9.16  tff(c_79, plain, (![A_36, B_35]: (r1_tarski(A_36, k2_xboole_0(B_35, A_36)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_42])).
% 16.79/9.16  tff(c_55989, plain, (r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_55658, c_79])).
% 16.79/9.16  tff(c_56073, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_55989, c_2698])).
% 16.79/9.16  tff(c_56080, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16407, c_56073])).
% 16.79/9.16  tff(c_15378, plain, (![A_322, B_323]: (k4_xboole_0(k2_xboole_0(A_322, B_323), k4_xboole_0(B_323, A_322))=k4_xboole_0(A_322, k4_xboole_0(B_323, A_322)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_349])).
% 16.79/9.16  tff(c_15588, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(A_1, B_2))=k4_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_15378])).
% 16.79/9.16  tff(c_56114, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), k1_xboole_0)=k4_xboole_0('#skF_5', k4_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56080, c_15588])).
% 16.79/9.16  tff(c_56313, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_268, c_56080, c_268, c_56114])).
% 16.79/9.16  tff(c_56776, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_56313, c_42])).
% 16.79/9.16  tff(c_56845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_56776])).
% 16.79/9.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.79/9.16  
% 16.79/9.16  Inference rules
% 16.79/9.16  ----------------------
% 16.79/9.16  #Ref     : 0
% 16.79/9.16  #Sup     : 14078
% 16.79/9.16  #Fact    : 0
% 16.79/9.16  #Define  : 0
% 16.79/9.16  #Split   : 3
% 16.79/9.16  #Chain   : 0
% 16.79/9.16  #Close   : 0
% 16.79/9.16  
% 16.79/9.16  Ordering : KBO
% 16.79/9.16  
% 16.79/9.16  Simplification rules
% 16.79/9.16  ----------------------
% 16.79/9.16  #Subsume      : 1220
% 16.79/9.16  #Demod        : 20200
% 16.79/9.16  #Tautology    : 7540
% 16.79/9.16  #SimpNegUnit  : 1
% 16.79/9.16  #BackRed      : 72
% 16.79/9.16  
% 16.79/9.16  #Partial instantiations: 0
% 16.79/9.16  #Strategies tried      : 1
% 16.79/9.16  
% 16.79/9.16  Timing (in seconds)
% 16.79/9.16  ----------------------
% 16.79/9.17  Preprocessing        : 0.36
% 16.79/9.17  Parsing              : 0.19
% 16.79/9.17  CNF conversion       : 0.03
% 16.79/9.17  Main loop            : 8.10
% 16.79/9.17  Inferencing          : 1.09
% 16.79/9.17  Reduction            : 4.93
% 16.79/9.17  Demodulation         : 4.51
% 16.79/9.17  BG Simplification    : 0.15
% 16.79/9.17  Subsumption          : 1.58
% 16.79/9.17  Abstraction          : 0.22
% 16.79/9.17  MUC search           : 0.00
% 16.79/9.17  Cooper               : 0.00
% 16.79/9.17  Total                : 8.50
% 16.79/9.17  Index Insertion      : 0.00
% 16.79/9.17  Index Deletion       : 0.00
% 16.79/9.17  Index Matching       : 0.00
% 16.79/9.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
