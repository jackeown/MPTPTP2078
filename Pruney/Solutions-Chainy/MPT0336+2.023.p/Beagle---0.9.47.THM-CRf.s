%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:03 EST 2020

% Result     : Theorem 18.05s
% Output     : CNFRefutation 18.13s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 144 expanded)
%              Number of leaves         :   31 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 248 expanded)
%              Number of equality atoms :   22 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_64,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_157,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,(
    k3_xboole_0('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_157])).

tff(c_253,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_259,plain,(
    ! [C_62] :
      ( ~ r1_xboole_0('#skF_7','#skF_6')
      | ~ r2_hidden(C_62,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_253])).

tff(c_263,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_259])).

tff(c_66,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_128,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = A_45
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_136,plain,(
    k4_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_64,c_128])).

tff(c_292,plain,(
    ! [D_67,B_68,A_69] :
      ( ~ r2_hidden(D_67,B_68)
      | ~ r2_hidden(D_67,k4_xboole_0(A_69,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_302,plain,(
    ! [D_70] :
      ( ~ r2_hidden(D_70,'#skF_6')
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_292])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_302])).

tff(c_68,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_6'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1181,plain,(
    ! [A_116,C_117,B_118] :
      ( r1_xboole_0(A_116,k4_xboole_0(C_117,B_118))
      | ~ r1_tarski(A_116,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3286,plain,(
    ! [A_267,C_268,B_269] :
      ( k4_xboole_0(A_267,k4_xboole_0(C_268,B_269)) = A_267
      | ~ r1_tarski(A_267,B_269) ) ),
    inference(resolution,[status(thm)],[c_1181,c_48])).

tff(c_40,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3426,plain,(
    ! [C_270,B_271] :
      ( k3_xboole_0(C_270,B_271) = C_270
      | ~ r1_tarski(C_270,B_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3286,c_40])).

tff(c_3430,plain,(
    k3_xboole_0(k3_xboole_0('#skF_5','#skF_6'),k1_tarski('#skF_8')) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_3426])).

tff(c_60,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,k1_tarski(B_38)) = A_37
      | r2_hidden(B_38,A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1608,plain,(
    ! [A_155,B_156] :
      ( k3_xboole_0(A_155,B_156) = k1_xboole_0
      | k4_xboole_0(A_155,B_156) != A_155 ) ),
    inference(resolution,[status(thm)],[c_50,c_157])).

tff(c_1630,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,k1_tarski(B_38)) = k1_xboole_0
      | r2_hidden(B_38,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1608])).

tff(c_3434,plain,
    ( k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0
    | r2_hidden('#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3430,c_1630])).

tff(c_3743,plain,(
    r2_hidden('#skF_8',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3434])).

tff(c_1021,plain,(
    ! [D_106,A_107,B_108] :
      ( r2_hidden(D_106,A_107)
      | ~ r2_hidden(D_106,k4_xboole_0(A_107,B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1037,plain,(
    ! [D_106,A_24,B_25] :
      ( r2_hidden(D_106,A_24)
      | ~ r2_hidden(D_106,k3_xboole_0(A_24,B_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1021])).

tff(c_3768,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_3743,c_1037])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_378,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4392,plain,(
    ! [D_311,A_312,B_313] :
      ( ~ r2_hidden(D_311,k4_xboole_0(A_312,B_313))
      | ~ r2_hidden(D_311,k3_xboole_0(A_312,B_313)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_6])).

tff(c_66652,plain,(
    ! [D_1081,A_1082,B_1083] :
      ( ~ r2_hidden(D_1081,k3_xboole_0(A_1082,B_1083))
      | r2_hidden(D_1081,B_1083)
      | ~ r2_hidden(D_1081,A_1082) ) ),
    inference(resolution,[status(thm)],[c_4,c_4392])).

tff(c_66896,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_3743,c_66652])).

tff(c_66988,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_66896])).

tff(c_66990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_66988])).

tff(c_66991,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3434])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_4'(A_18,B_19),k3_xboole_0(A_18,B_19))
      | r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_67010,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_xboole_0)
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_66991,c_34])).

tff(c_67037,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_67010])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67055,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_67037,c_26])).

tff(c_87,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_87])).

tff(c_1726,plain,(
    ! [A_163,C_164,B_165] :
      ( ~ r1_xboole_0(A_163,C_164)
      | ~ r1_xboole_0(A_163,B_165)
      | r1_xboole_0(A_163,k2_xboole_0(B_165,C_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_68568,plain,(
    ! [B_1159,C_1160,A_1161] :
      ( r1_xboole_0(k2_xboole_0(B_1159,C_1160),A_1161)
      | ~ r1_xboole_0(A_1161,C_1160)
      | ~ r1_xboole_0(A_1161,B_1159) ) ),
    inference(resolution,[status(thm)],[c_1726,c_26])).

tff(c_62,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_68598,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_7')
    | ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_68568,c_62])).

tff(c_68617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67055,c_90,c_68598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.05/9.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.05/9.91  
% 18.05/9.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.13/9.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 18.13/9.92  
% 18.13/9.92  %Foreground sorts:
% 18.13/9.92  
% 18.13/9.92  
% 18.13/9.92  %Background operators:
% 18.13/9.92  
% 18.13/9.92  
% 18.13/9.92  %Foreground operators:
% 18.13/9.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.13/9.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.13/9.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.13/9.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.13/9.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.13/9.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.13/9.92  tff('#skF_7', type, '#skF_7': $i).
% 18.13/9.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.13/9.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.13/9.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.13/9.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.13/9.92  tff('#skF_5', type, '#skF_5': $i).
% 18.13/9.92  tff('#skF_6', type, '#skF_6': $i).
% 18.13/9.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.13/9.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.13/9.92  tff('#skF_8', type, '#skF_8': $i).
% 18.13/9.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.13/9.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.13/9.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.13/9.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.13/9.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 18.13/9.92  
% 18.13/9.93  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 18.13/9.93  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 18.13/9.93  tff(f_77, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 18.13/9.93  tff(f_101, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 18.13/9.93  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 18.13/9.93  tff(f_105, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 18.13/9.93  tff(f_81, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.13/9.93  tff(f_114, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 18.13/9.93  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 18.13/9.93  tff(f_97, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 18.13/9.93  tff(c_64, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.13/9.93  tff(c_157, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.13/9.93  tff(c_169, plain, (k3_xboole_0('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_157])).
% 18.13/9.93  tff(c_253, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.13/9.93  tff(c_259, plain, (![C_62]: (~r1_xboole_0('#skF_7', '#skF_6') | ~r2_hidden(C_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_169, c_253])).
% 18.13/9.93  tff(c_263, plain, (![C_62]: (~r2_hidden(C_62, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_259])).
% 18.13/9.93  tff(c_66, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.13/9.93  tff(c_128, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=A_45 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.13/9.93  tff(c_136, plain, (k4_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_64, c_128])).
% 18.13/9.93  tff(c_292, plain, (![D_67, B_68, A_69]: (~r2_hidden(D_67, B_68) | ~r2_hidden(D_67, k4_xboole_0(A_69, B_68)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.13/9.93  tff(c_302, plain, (![D_70]: (~r2_hidden(D_70, '#skF_6') | ~r2_hidden(D_70, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_292])).
% 18.13/9.93  tff(c_306, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_302])).
% 18.13/9.93  tff(c_68, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.13/9.93  tff(c_1181, plain, (![A_116, C_117, B_118]: (r1_xboole_0(A_116, k4_xboole_0(C_117, B_118)) | ~r1_tarski(A_116, B_118))), inference(cnfTransformation, [status(thm)], [f_105])).
% 18.13/9.93  tff(c_48, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.13/9.93  tff(c_3286, plain, (![A_267, C_268, B_269]: (k4_xboole_0(A_267, k4_xboole_0(C_268, B_269))=A_267 | ~r1_tarski(A_267, B_269))), inference(resolution, [status(thm)], [c_1181, c_48])).
% 18.13/9.93  tff(c_40, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.13/9.93  tff(c_3426, plain, (![C_270, B_271]: (k3_xboole_0(C_270, B_271)=C_270 | ~r1_tarski(C_270, B_271))), inference(superposition, [status(thm), theory('equality')], [c_3286, c_40])).
% 18.13/9.93  tff(c_3430, plain, (k3_xboole_0(k3_xboole_0('#skF_5', '#skF_6'), k1_tarski('#skF_8'))=k3_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_3426])).
% 18.13/9.93  tff(c_60, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k1_tarski(B_38))=A_37 | r2_hidden(B_38, A_37))), inference(cnfTransformation, [status(thm)], [f_114])).
% 18.13/9.93  tff(c_50, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k4_xboole_0(A_29, B_30)!=A_29)), inference(cnfTransformation, [status(thm)], [f_101])).
% 18.13/9.93  tff(c_1608, plain, (![A_155, B_156]: (k3_xboole_0(A_155, B_156)=k1_xboole_0 | k4_xboole_0(A_155, B_156)!=A_155)), inference(resolution, [status(thm)], [c_50, c_157])).
% 18.13/9.93  tff(c_1630, plain, (![A_37, B_38]: (k3_xboole_0(A_37, k1_tarski(B_38))=k1_xboole_0 | r2_hidden(B_38, A_37))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1608])).
% 18.13/9.93  tff(c_3434, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0 | r2_hidden('#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3430, c_1630])).
% 18.13/9.93  tff(c_3743, plain, (r2_hidden('#skF_8', k3_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_3434])).
% 18.13/9.93  tff(c_1021, plain, (![D_106, A_107, B_108]: (r2_hidden(D_106, A_107) | ~r2_hidden(D_106, k4_xboole_0(A_107, B_108)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.13/9.93  tff(c_1037, plain, (![D_106, A_24, B_25]: (r2_hidden(D_106, A_24) | ~r2_hidden(D_106, k3_xboole_0(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1021])).
% 18.13/9.93  tff(c_3768, plain, (r2_hidden('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_3743, c_1037])).
% 18.13/9.93  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.13/9.93  tff(c_378, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.13/9.93  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.13/9.93  tff(c_4392, plain, (![D_311, A_312, B_313]: (~r2_hidden(D_311, k4_xboole_0(A_312, B_313)) | ~r2_hidden(D_311, k3_xboole_0(A_312, B_313)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_6])).
% 18.13/9.93  tff(c_66652, plain, (![D_1081, A_1082, B_1083]: (~r2_hidden(D_1081, k3_xboole_0(A_1082, B_1083)) | r2_hidden(D_1081, B_1083) | ~r2_hidden(D_1081, A_1082))), inference(resolution, [status(thm)], [c_4, c_4392])).
% 18.13/9.93  tff(c_66896, plain, (r2_hidden('#skF_8', '#skF_6') | ~r2_hidden('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_3743, c_66652])).
% 18.13/9.93  tff(c_66988, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_66896])).
% 18.13/9.93  tff(c_66990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_66988])).
% 18.13/9.93  tff(c_66991, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3434])).
% 18.13/9.93  tff(c_34, plain, (![A_18, B_19]: (r2_hidden('#skF_4'(A_18, B_19), k3_xboole_0(A_18, B_19)) | r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.13/9.93  tff(c_67010, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_xboole_0) | r1_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_66991, c_34])).
% 18.13/9.93  tff(c_67037, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_263, c_67010])).
% 18.13/9.93  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.13/9.93  tff(c_67055, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_67037, c_26])).
% 18.13/9.93  tff(c_87, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.13/9.93  tff(c_90, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_87])).
% 18.13/9.93  tff(c_1726, plain, (![A_163, C_164, B_165]: (~r1_xboole_0(A_163, C_164) | ~r1_xboole_0(A_163, B_165) | r1_xboole_0(A_163, k2_xboole_0(B_165, C_164)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.13/9.93  tff(c_68568, plain, (![B_1159, C_1160, A_1161]: (r1_xboole_0(k2_xboole_0(B_1159, C_1160), A_1161) | ~r1_xboole_0(A_1161, C_1160) | ~r1_xboole_0(A_1161, B_1159))), inference(resolution, [status(thm)], [c_1726, c_26])).
% 18.13/9.93  tff(c_62, plain, (~r1_xboole_0(k2_xboole_0('#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.13/9.93  tff(c_68598, plain, (~r1_xboole_0('#skF_6', '#skF_7') | ~r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_68568, c_62])).
% 18.13/9.93  tff(c_68617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67055, c_90, c_68598])).
% 18.13/9.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.13/9.93  
% 18.13/9.93  Inference rules
% 18.13/9.93  ----------------------
% 18.13/9.93  #Ref     : 0
% 18.13/9.93  #Sup     : 17032
% 18.13/9.93  #Fact    : 0
% 18.13/9.93  #Define  : 0
% 18.13/9.93  #Split   : 8
% 18.13/9.93  #Chain   : 0
% 18.13/9.93  #Close   : 0
% 18.13/9.93  
% 18.13/9.93  Ordering : KBO
% 18.13/9.93  
% 18.13/9.93  Simplification rules
% 18.13/9.93  ----------------------
% 18.13/9.93  #Subsume      : 5209
% 18.13/9.93  #Demod        : 10455
% 18.13/9.93  #Tautology    : 7298
% 18.13/9.93  #SimpNegUnit  : 648
% 18.13/9.93  #BackRed      : 26
% 18.13/9.93  
% 18.13/9.93  #Partial instantiations: 0
% 18.13/9.93  #Strategies tried      : 1
% 18.13/9.93  
% 18.13/9.93  Timing (in seconds)
% 18.13/9.93  ----------------------
% 18.13/9.93  Preprocessing        : 0.32
% 18.13/9.93  Parsing              : 0.17
% 18.13/9.93  CNF conversion       : 0.02
% 18.13/9.93  Main loop            : 8.83
% 18.13/9.93  Inferencing          : 1.34
% 18.13/9.93  Reduction            : 4.14
% 18.13/9.93  Demodulation         : 3.14
% 18.13/9.93  BG Simplification    : 0.13
% 18.13/9.93  Subsumption          : 2.78
% 18.13/9.93  Abstraction          : 0.21
% 18.13/9.93  MUC search           : 0.00
% 18.13/9.93  Cooper               : 0.00
% 18.13/9.93  Total                : 9.19
% 18.13/9.94  Index Insertion      : 0.00
% 18.13/9.94  Index Deletion       : 0.00
% 18.13/9.94  Index Matching       : 0.00
% 18.13/9.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
