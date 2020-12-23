%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:16 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 452 expanded)
%              Number of leaves         :   21 ( 160 expanded)
%              Depth                    :   21
%              Number of atoms          :  119 (1345 expanded)
%              Number of equality atoms :   21 ( 185 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

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

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_32,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_9,B_32,C_33] :
      ( r2_hidden('#skF_3'(A_9,B_32,C_33),B_32)
      | r2_hidden('#skF_4'(A_9,B_32,C_33),C_33)
      | k10_relat_1(A_9,B_32) = C_33
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_9,B_32,D_47] :
      ( r2_hidden('#skF_5'(A_9,B_32,k10_relat_1(A_9,B_32),D_47),B_32)
      | ~ r2_hidden(D_47,k10_relat_1(A_9,B_32))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,(
    ! [A_80,B_81,D_82] :
      ( r2_hidden('#skF_5'(A_80,B_81,k10_relat_1(A_80,B_81),D_82),B_81)
      | ~ r2_hidden(D_82,k10_relat_1(A_80,B_81))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,B_61)
      | ~ r2_hidden(C_62,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | k4_xboole_0(A_65,B_64) != A_65 ) ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_68,plain,(
    ! [A_70,B_71,A_72] :
      ( ~ r2_hidden('#skF_1'(A_70,B_71),A_72)
      | k4_xboole_0(A_72,A_70) != A_72
      | r1_xboole_0(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_77,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,A_73) != A_73
      | r1_xboole_0(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_82,plain,(
    ! [B_75] : r1_xboole_0(k1_xboole_0,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_77])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [C_5,B_75] :
      ( ~ r2_hidden(C_5,B_75)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_287,plain,(
    ! [A_114,B_115,D_116] :
      ( ~ r2_hidden('#skF_5'(A_114,B_115,k10_relat_1(A_114,B_115),D_116),k1_xboole_0)
      | ~ r2_hidden(D_116,k10_relat_1(A_114,B_115))
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_106,c_88])).

tff(c_293,plain,(
    ! [D_117,A_118] :
      ( ~ r2_hidden(D_117,k10_relat_1(A_118,k1_xboole_0))
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_16,c_287])).

tff(c_902,plain,(
    ! [A_208,A_209,C_210] :
      ( ~ v1_relat_1(A_208)
      | r2_hidden('#skF_4'(A_209,k10_relat_1(A_208,k1_xboole_0),C_210),C_210)
      | k10_relat_1(A_209,k10_relat_1(A_208,k1_xboole_0)) = C_210
      | ~ v1_relat_1(A_209) ) ),
    inference(resolution,[status(thm)],[c_28,c_293])).

tff(c_292,plain,(
    ! [D_47,A_9] :
      ( ~ r2_hidden(D_47,k10_relat_1(A_9,k1_xboole_0))
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_287])).

tff(c_946,plain,(
    ! [A_216,A_217,A_218] :
      ( ~ v1_relat_1(A_216)
      | ~ v1_relat_1(A_217)
      | k10_relat_1(A_218,k10_relat_1(A_217,k1_xboole_0)) = k10_relat_1(A_216,k1_xboole_0)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_902,c_292])).

tff(c_950,plain,(
    ! [A_219,A_220] :
      ( ~ v1_relat_1(A_219)
      | k10_relat_1(A_220,k10_relat_1(A_219,k1_xboole_0)) = k10_relat_1('#skF_6',k1_xboole_0)
      | ~ v1_relat_1(A_220) ) ),
    inference(resolution,[status(thm)],[c_34,c_946])).

tff(c_326,plain,(
    ! [A_118,D_47,A_9] :
      ( ~ v1_relat_1(A_118)
      | ~ r2_hidden(D_47,k10_relat_1(A_9,k10_relat_1(A_118,k1_xboole_0)))
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_293])).

tff(c_1026,plain,(
    ! [A_219,D_47,A_220] :
      ( ~ v1_relat_1(A_219)
      | ~ r2_hidden(D_47,k10_relat_1('#skF_6',k1_xboole_0))
      | ~ v1_relat_1(A_220)
      | ~ v1_relat_1(A_219)
      | ~ v1_relat_1(A_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_326])).

tff(c_1277,plain,(
    ! [A_234] :
      ( ~ v1_relat_1(A_234)
      | ~ v1_relat_1(A_234) ) ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_1279,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_1277])).

tff(c_1283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1279])).

tff(c_1284,plain,(
    ! [D_47,A_219] :
      ( ~ r2_hidden(D_47,k10_relat_1('#skF_6',k1_xboole_0))
      | ~ v1_relat_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_1290,plain,(
    ! [A_240] :
      ( ~ v1_relat_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(splitLeft,[status(thm)],[c_1284])).

tff(c_1292,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_1290])).

tff(c_1296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1292])).

tff(c_1298,plain,(
    ! [D_241] : ~ r2_hidden(D_241,k10_relat_1('#skF_6',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1337,plain,(
    ! [A_9,C_33] :
      ( r2_hidden('#skF_4'(A_9,k10_relat_1('#skF_6',k1_xboole_0),C_33),C_33)
      | k10_relat_1(A_9,k10_relat_1('#skF_6',k1_xboole_0)) = C_33
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_28,c_1298])).

tff(c_1957,plain,(
    ! [A_270,C_271] :
      ( r2_hidden('#skF_4'(A_270,k10_relat_1('#skF_6',k1_xboole_0),C_271),C_271)
      | k10_relat_1(A_270,k10_relat_1('#skF_6',k1_xboole_0)) = C_271
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_28,c_1298])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [C_76,B_77] :
      ( ~ r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_148,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden('#skF_1'(A_86,B_87),k1_xboole_0)
      | r1_xboole_0(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_170,plain,(
    ! [A_91] : r1_xboole_0(A_91,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_176,plain,(
    ! [C_5,A_91] :
      ( ~ r2_hidden(C_5,k1_xboole_0)
      | ~ r2_hidden(C_5,A_91) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_3206,plain,(
    ! [A_309,A_310] :
      ( ~ r2_hidden('#skF_4'(A_309,k10_relat_1('#skF_6',k1_xboole_0),k1_xboole_0),A_310)
      | k10_relat_1(A_309,k10_relat_1('#skF_6',k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_309) ) ),
    inference(resolution,[status(thm)],[c_1957,c_176])).

tff(c_3226,plain,(
    ! [A_311] :
      ( k10_relat_1(A_311,k10_relat_1('#skF_6',k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_311) ) ),
    inference(resolution,[status(thm)],[c_1337,c_3206])).

tff(c_949,plain,(
    ! [A_217,A_218] :
      ( ~ v1_relat_1(A_217)
      | k10_relat_1(A_218,k10_relat_1(A_217,k1_xboole_0)) = k10_relat_1('#skF_6',k1_xboole_0)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_34,c_946])).

tff(c_3292,plain,(
    ! [A_311] :
      ( ~ v1_relat_1('#skF_6')
      | k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_311)
      | ~ v1_relat_1(A_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3226,c_949])).

tff(c_3397,plain,(
    ! [A_311] :
      ( k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3292])).

tff(c_3398,plain,(
    ! [A_311] : ~ v1_relat_1(A_311) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3397])).

tff(c_3429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3398,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.84  
% 4.77/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.84  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 4.77/1.84  
% 4.77/1.84  %Foreground sorts:
% 4.77/1.84  
% 4.77/1.84  
% 4.77/1.84  %Background operators:
% 4.77/1.84  
% 4.77/1.84  
% 4.77/1.84  %Foreground operators:
% 4.77/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.77/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.77/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.84  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.77/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.77/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.77/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.77/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.77/1.84  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.77/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.77/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.77/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.77/1.84  
% 4.77/1.86  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 4.77/1.86  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 4.77/1.86  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.77/1.86  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.77/1.86  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.77/1.86  tff(c_32, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.77/1.86  tff(c_34, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.77/1.86  tff(c_28, plain, (![A_9, B_32, C_33]: (r2_hidden('#skF_3'(A_9, B_32, C_33), B_32) | r2_hidden('#skF_4'(A_9, B_32, C_33), C_33) | k10_relat_1(A_9, B_32)=C_33 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.77/1.86  tff(c_16, plain, (![A_9, B_32, D_47]: (r2_hidden('#skF_5'(A_9, B_32, k10_relat_1(A_9, B_32), D_47), B_32) | ~r2_hidden(D_47, k10_relat_1(A_9, B_32)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.77/1.86  tff(c_106, plain, (![A_80, B_81, D_82]: (r2_hidden('#skF_5'(A_80, B_81, k10_relat_1(A_80, B_81), D_82), B_81) | ~r2_hidden(D_82, k10_relat_1(A_80, B_81)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.77/1.86  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.77/1.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.86  tff(c_12, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.77/1.86  tff(c_50, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, B_61) | ~r2_hidden(C_62, A_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.86  tff(c_54, plain, (![C_63, B_64, A_65]: (~r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | k4_xboole_0(A_65, B_64)!=A_65)), inference(resolution, [status(thm)], [c_12, c_50])).
% 4.77/1.86  tff(c_68, plain, (![A_70, B_71, A_72]: (~r2_hidden('#skF_1'(A_70, B_71), A_72) | k4_xboole_0(A_72, A_70)!=A_72 | r1_xboole_0(A_70, B_71))), inference(resolution, [status(thm)], [c_6, c_54])).
% 4.77/1.86  tff(c_77, plain, (![A_73, B_74]: (k4_xboole_0(A_73, A_73)!=A_73 | r1_xboole_0(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_68])).
% 4.77/1.86  tff(c_82, plain, (![B_75]: (r1_xboole_0(k1_xboole_0, B_75))), inference(superposition, [status(thm), theory('equality')], [c_8, c_77])).
% 4.77/1.86  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.86  tff(c_88, plain, (![C_5, B_75]: (~r2_hidden(C_5, B_75) | ~r2_hidden(C_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_82, c_2])).
% 4.77/1.86  tff(c_287, plain, (![A_114, B_115, D_116]: (~r2_hidden('#skF_5'(A_114, B_115, k10_relat_1(A_114, B_115), D_116), k1_xboole_0) | ~r2_hidden(D_116, k10_relat_1(A_114, B_115)) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_106, c_88])).
% 4.77/1.86  tff(c_293, plain, (![D_117, A_118]: (~r2_hidden(D_117, k10_relat_1(A_118, k1_xboole_0)) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_16, c_287])).
% 4.77/1.86  tff(c_902, plain, (![A_208, A_209, C_210]: (~v1_relat_1(A_208) | r2_hidden('#skF_4'(A_209, k10_relat_1(A_208, k1_xboole_0), C_210), C_210) | k10_relat_1(A_209, k10_relat_1(A_208, k1_xboole_0))=C_210 | ~v1_relat_1(A_209))), inference(resolution, [status(thm)], [c_28, c_293])).
% 4.77/1.86  tff(c_292, plain, (![D_47, A_9]: (~r2_hidden(D_47, k10_relat_1(A_9, k1_xboole_0)) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_287])).
% 4.77/1.86  tff(c_946, plain, (![A_216, A_217, A_218]: (~v1_relat_1(A_216) | ~v1_relat_1(A_217) | k10_relat_1(A_218, k10_relat_1(A_217, k1_xboole_0))=k10_relat_1(A_216, k1_xboole_0) | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_902, c_292])).
% 4.77/1.86  tff(c_950, plain, (![A_219, A_220]: (~v1_relat_1(A_219) | k10_relat_1(A_220, k10_relat_1(A_219, k1_xboole_0))=k10_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1(A_220))), inference(resolution, [status(thm)], [c_34, c_946])).
% 4.77/1.86  tff(c_326, plain, (![A_118, D_47, A_9]: (~v1_relat_1(A_118) | ~r2_hidden(D_47, k10_relat_1(A_9, k10_relat_1(A_118, k1_xboole_0))) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_293])).
% 4.77/1.86  tff(c_1026, plain, (![A_219, D_47, A_220]: (~v1_relat_1(A_219) | ~r2_hidden(D_47, k10_relat_1('#skF_6', k1_xboole_0)) | ~v1_relat_1(A_220) | ~v1_relat_1(A_219) | ~v1_relat_1(A_220))), inference(superposition, [status(thm), theory('equality')], [c_950, c_326])).
% 4.77/1.86  tff(c_1277, plain, (![A_234]: (~v1_relat_1(A_234) | ~v1_relat_1(A_234))), inference(splitLeft, [status(thm)], [c_1026])).
% 4.77/1.86  tff(c_1279, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_1277])).
% 4.77/1.86  tff(c_1283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1279])).
% 4.77/1.86  tff(c_1284, plain, (![D_47, A_219]: (~r2_hidden(D_47, k10_relat_1('#skF_6', k1_xboole_0)) | ~v1_relat_1(A_219) | ~v1_relat_1(A_219))), inference(splitRight, [status(thm)], [c_1026])).
% 4.77/1.86  tff(c_1290, plain, (![A_240]: (~v1_relat_1(A_240) | ~v1_relat_1(A_240))), inference(splitLeft, [status(thm)], [c_1284])).
% 4.77/1.86  tff(c_1292, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_1290])).
% 4.77/1.86  tff(c_1296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1292])).
% 4.77/1.86  tff(c_1298, plain, (![D_241]: (~r2_hidden(D_241, k10_relat_1('#skF_6', k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1284])).
% 4.77/1.86  tff(c_1337, plain, (![A_9, C_33]: (r2_hidden('#skF_4'(A_9, k10_relat_1('#skF_6', k1_xboole_0), C_33), C_33) | k10_relat_1(A_9, k10_relat_1('#skF_6', k1_xboole_0))=C_33 | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_28, c_1298])).
% 4.77/1.86  tff(c_1957, plain, (![A_270, C_271]: (r2_hidden('#skF_4'(A_270, k10_relat_1('#skF_6', k1_xboole_0), C_271), C_271) | k10_relat_1(A_270, k10_relat_1('#skF_6', k1_xboole_0))=C_271 | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_28, c_1298])).
% 4.77/1.86  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.86  tff(c_91, plain, (![C_76, B_77]: (~r2_hidden(C_76, B_77) | ~r2_hidden(C_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_82, c_2])).
% 4.77/1.86  tff(c_148, plain, (![A_86, B_87]: (~r2_hidden('#skF_1'(A_86, B_87), k1_xboole_0) | r1_xboole_0(A_86, B_87))), inference(resolution, [status(thm)], [c_4, c_91])).
% 4.77/1.86  tff(c_170, plain, (![A_91]: (r1_xboole_0(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_148])).
% 4.77/1.86  tff(c_176, plain, (![C_5, A_91]: (~r2_hidden(C_5, k1_xboole_0) | ~r2_hidden(C_5, A_91))), inference(resolution, [status(thm)], [c_170, c_2])).
% 4.77/1.86  tff(c_3206, plain, (![A_309, A_310]: (~r2_hidden('#skF_4'(A_309, k10_relat_1('#skF_6', k1_xboole_0), k1_xboole_0), A_310) | k10_relat_1(A_309, k10_relat_1('#skF_6', k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_309))), inference(resolution, [status(thm)], [c_1957, c_176])).
% 4.77/1.86  tff(c_3226, plain, (![A_311]: (k10_relat_1(A_311, k10_relat_1('#skF_6', k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_311))), inference(resolution, [status(thm)], [c_1337, c_3206])).
% 4.77/1.86  tff(c_949, plain, (![A_217, A_218]: (~v1_relat_1(A_217) | k10_relat_1(A_218, k10_relat_1(A_217, k1_xboole_0))=k10_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_34, c_946])).
% 4.77/1.86  tff(c_3292, plain, (![A_311]: (~v1_relat_1('#skF_6') | k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_311) | ~v1_relat_1(A_311))), inference(superposition, [status(thm), theory('equality')], [c_3226, c_949])).
% 4.77/1.86  tff(c_3397, plain, (![A_311]: (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_311))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3292])).
% 4.77/1.86  tff(c_3398, plain, (![A_311]: (~v1_relat_1(A_311))), inference(negUnitSimplification, [status(thm)], [c_32, c_3397])).
% 4.77/1.86  tff(c_3429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3398, c_34])).
% 4.77/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.86  
% 4.77/1.86  Inference rules
% 4.77/1.86  ----------------------
% 4.77/1.86  #Ref     : 0
% 4.77/1.86  #Sup     : 772
% 4.77/1.86  #Fact    : 0
% 4.77/1.86  #Define  : 0
% 4.77/1.86  #Split   : 10
% 4.77/1.86  #Chain   : 0
% 4.77/1.86  #Close   : 0
% 4.77/1.86  
% 4.77/1.86  Ordering : KBO
% 4.77/1.86  
% 4.77/1.86  Simplification rules
% 4.77/1.86  ----------------------
% 4.77/1.86  #Subsume      : 551
% 4.77/1.86  #Demod        : 197
% 4.77/1.86  #Tautology    : 210
% 4.77/1.86  #SimpNegUnit  : 13
% 4.77/1.86  #BackRed      : 4
% 4.77/1.86  
% 4.77/1.86  #Partial instantiations: 0
% 4.77/1.86  #Strategies tried      : 1
% 4.77/1.86  
% 4.77/1.86  Timing (in seconds)
% 4.77/1.86  ----------------------
% 4.77/1.86  Preprocessing        : 0.29
% 4.77/1.86  Parsing              : 0.15
% 4.77/1.86  CNF conversion       : 0.03
% 4.77/1.86  Main loop            : 0.82
% 4.77/1.86  Inferencing          : 0.30
% 4.77/1.86  Reduction            : 0.19
% 4.77/1.86  Demodulation         : 0.13
% 4.77/1.86  BG Simplification    : 0.03
% 4.77/1.86  Subsumption          : 0.25
% 4.77/1.86  Abstraction          : 0.04
% 4.77/1.86  MUC search           : 0.00
% 4.77/1.86  Cooper               : 0.00
% 4.77/1.86  Total                : 1.14
% 4.77/1.86  Index Insertion      : 0.00
% 4.77/1.86  Index Deletion       : 0.00
% 4.77/1.86  Index Matching       : 0.00
% 4.77/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
