%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:53 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   52 (  86 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 153 expanded)
%              Number of equality atoms :    2 (  16 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( ~ r1_xboole_0(k4_zfmisc_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
       => ( ~ r1_xboole_0(A,E)
          & ~ r1_xboole_0(B,F)
          & ~ r1_xboole_0(C,G)
          & ~ r1_xboole_0(D,H) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] :
      ( ~ r1_xboole_0(k3_zfmisc_1(A,B,C),k3_zfmisc_1(D,E,F))
     => ( ~ r1_xboole_0(A,D)
        & ~ r1_xboole_0(B,E)
        & ~ r1_xboole_0(C,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_mcart_1)).

tff(c_14,plain,
    ( r1_xboole_0('#skF_4','#skF_8')
    | r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_2','#skF_6')
    | r1_xboole_0('#skF_1','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_35,plain,(
    r1_xboole_0('#skF_1','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13,D_14) = k4_zfmisc_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [F_34,A_37,D_33,B_35,C_36,E_38] :
      ( ~ r1_xboole_0(A_37,D_33)
      | r1_xboole_0(k3_zfmisc_1(A_37,B_35,C_36),k3_zfmisc_1(D_33,E_38,F_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [F_84,C_81,A_83,D_86,B_85,E_82,D_87] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_83,B_85),D_87)
      | r1_xboole_0(k4_zfmisc_1(A_83,B_85,C_81,D_86),k3_zfmisc_1(D_87,E_82,F_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_36])).

tff(c_84,plain,(
    ! [C_103,D_109,B_107,C_104,A_110,D_108,A_105,B_106] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_110,B_107),k2_zfmisc_1(A_105,B_106))
      | r1_xboole_0(k4_zfmisc_1(A_110,B_107,C_104,D_109),k4_zfmisc_1(A_105,B_106,C_103,D_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_16])).

tff(c_94,plain,(
    ~ r1_xboole_0('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_94])).

tff(c_100,plain,
    ( r1_xboole_0('#skF_2','#skF_6')
    | r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_102,plain,(
    r1_xboole_0('#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_110,plain,(
    ! [A_121,E_122,F_118,B_119,C_120,D_117] :
      ( ~ r1_xboole_0(C_120,F_118)
      | r1_xboole_0(k3_zfmisc_1(A_121,B_119,C_120),k3_zfmisc_1(D_117,E_122,F_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [A_134,C_132,A_130,C_133,B_131,D_136,B_135] :
      ( ~ r1_xboole_0(C_133,D_136)
      | r1_xboole_0(k3_zfmisc_1(A_130,B_131,C_133),k4_zfmisc_1(A_134,B_135,C_132,D_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_138,plain,(
    ! [A_163,B_161,C_160,C_159,D_166,D_165,B_164,A_162] :
      ( ~ r1_xboole_0(D_165,D_166)
      | r1_xboole_0(k4_zfmisc_1(A_163,B_164,C_160,D_165),k4_zfmisc_1(A_162,B_161,C_159,D_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_141,plain,(
    ~ r1_xboole_0('#skF_4','#skF_8') ),
    inference(resolution,[status(thm)],[c_138,c_16])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_141])).

tff(c_146,plain,
    ( r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_2','#skF_6') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_148,plain,(
    r1_xboole_0('#skF_2','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_2,plain,(
    ! [C_3,D_4,A_1,B_2] :
      ( ~ r1_xboole_0(C_3,D_4)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [C_170,A_171,F_168,D_167,B_169,E_172] :
      ( ~ r1_xboole_0(A_171,D_167)
      | r1_xboole_0(k3_zfmisc_1(A_171,B_169,C_170),k3_zfmisc_1(D_167,E_172,F_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_184,plain,(
    ! [D_217,C_216,D_221,B_220,F_218,A_219,E_215] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_219,B_220),D_217)
      | r1_xboole_0(k4_zfmisc_1(A_219,B_220,C_216,D_221),k3_zfmisc_1(D_217,E_215,F_218)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_149])).

tff(c_197,plain,(
    ! [C_238,D_243,B_244,A_240,B_242,A_237,C_239,D_241] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_237,B_244),k2_zfmisc_1(A_240,B_242))
      | r1_xboole_0(k4_zfmisc_1(A_237,B_244,C_239,D_241),k4_zfmisc_1(A_240,B_242,C_238,D_243)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_184])).

tff(c_201,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_197,c_16])).

tff(c_204,plain,(
    ~ r1_xboole_0('#skF_2','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_201])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_204])).

tff(c_212,plain,(
    r1_xboole_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_28,plain,(
    ! [C_30,A_31,E_32,D_27,F_28,B_29] :
      ( ~ r1_xboole_0(B_29,E_32)
      | r1_xboole_0(k3_zfmisc_1(A_31,B_29,C_30),k3_zfmisc_1(D_27,E_32,F_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_240,plain,(
    ! [A_279,D_284,C_278,B_283,C_280,A_281,B_282] :
      ( ~ r1_xboole_0(B_283,C_278)
      | r1_xboole_0(k3_zfmisc_1(A_279,B_283,C_280),k4_zfmisc_1(A_281,B_282,C_278,D_284)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_249,plain,(
    ! [C_296,A_293,D_299,C_294,D_300,B_298,A_297,B_295] :
      ( ~ r1_xboole_0(C_294,C_296)
      | r1_xboole_0(k4_zfmisc_1(A_297,B_298,C_294,D_299),k4_zfmisc_1(A_293,B_295,C_296,D_300)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_240])).

tff(c_252,plain,(
    ~ r1_xboole_0('#skF_3','#skF_7') ),
    inference(resolution,[status(thm)],[c_249,c_16])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:04:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.34  
% 2.28/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.34  %$ r1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.28/1.34  
% 2.28/1.34  %Foreground sorts:
% 2.28/1.34  
% 2.28/1.34  
% 2.28/1.34  %Background operators:
% 2.28/1.34  
% 2.28/1.34  
% 2.28/1.34  %Foreground operators:
% 2.28/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.34  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.28/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.28/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.34  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.28/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.28/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.34  
% 2.28/1.35  tff(f_61, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (~r1_xboole_0(k4_zfmisc_1(A, B, C, D), k4_zfmisc_1(E, F, G, H)) => (((~r1_xboole_0(A, E) & ~r1_xboole_0(B, F)) & ~r1_xboole_0(C, G)) & ~r1_xboole_0(D, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_mcart_1)).
% 2.28/1.35  tff(f_31, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.28/1.35  tff(f_45, axiom, (![A, B, C, D]: (k3_zfmisc_1(k2_zfmisc_1(A, B), C, D) = k4_zfmisc_1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_mcart_1)).
% 2.28/1.35  tff(f_43, axiom, (![A, B, C, D, E, F]: (~r1_xboole_0(k3_zfmisc_1(A, B, C), k3_zfmisc_1(D, E, F)) => ((~r1_xboole_0(A, D) & ~r1_xboole_0(B, E)) & ~r1_xboole_0(C, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_mcart_1)).
% 2.28/1.35  tff(c_14, plain, (r1_xboole_0('#skF_4', '#skF_8') | r1_xboole_0('#skF_3', '#skF_7') | r1_xboole_0('#skF_2', '#skF_6') | r1_xboole_0('#skF_1', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.28/1.35  tff(c_35, plain, (r1_xboole_0('#skF_1', '#skF_5')), inference(splitLeft, [status(thm)], [c_14])).
% 2.28/1.35  tff(c_4, plain, (![A_1, B_2, C_3, D_4]: (~r1_xboole_0(A_1, B_2) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.35  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k3_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13, D_14)=k4_zfmisc_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.35  tff(c_36, plain, (![F_34, A_37, D_33, B_35, C_36, E_38]: (~r1_xboole_0(A_37, D_33) | r1_xboole_0(k3_zfmisc_1(A_37, B_35, C_36), k3_zfmisc_1(D_33, E_38, F_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.35  tff(c_71, plain, (![F_84, C_81, A_83, D_86, B_85, E_82, D_87]: (~r1_xboole_0(k2_zfmisc_1(A_83, B_85), D_87) | r1_xboole_0(k4_zfmisc_1(A_83, B_85, C_81, D_86), k3_zfmisc_1(D_87, E_82, F_84)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_36])).
% 2.28/1.35  tff(c_84, plain, (![C_103, D_109, B_107, C_104, A_110, D_108, A_105, B_106]: (~r1_xboole_0(k2_zfmisc_1(A_110, B_107), k2_zfmisc_1(A_105, B_106)) | r1_xboole_0(k4_zfmisc_1(A_110, B_107, C_104, D_109), k4_zfmisc_1(A_105, B_106, C_103, D_108)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_71])).
% 2.28/1.35  tff(c_16, plain, (~r1_xboole_0(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.28/1.35  tff(c_88, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_84, c_16])).
% 2.28/1.35  tff(c_94, plain, (~r1_xboole_0('#skF_1', '#skF_5')), inference(resolution, [status(thm)], [c_4, c_88])).
% 2.28/1.35  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_94])).
% 2.28/1.35  tff(c_100, plain, (r1_xboole_0('#skF_2', '#skF_6') | r1_xboole_0('#skF_3', '#skF_7') | r1_xboole_0('#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_14])).
% 2.28/1.35  tff(c_102, plain, (r1_xboole_0('#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_100])).
% 2.28/1.35  tff(c_110, plain, (![A_121, E_122, F_118, B_119, C_120, D_117]: (~r1_xboole_0(C_120, F_118) | r1_xboole_0(k3_zfmisc_1(A_121, B_119, C_120), k3_zfmisc_1(D_117, E_122, F_118)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.35  tff(c_121, plain, (![A_134, C_132, A_130, C_133, B_131, D_136, B_135]: (~r1_xboole_0(C_133, D_136) | r1_xboole_0(k3_zfmisc_1(A_130, B_131, C_133), k4_zfmisc_1(A_134, B_135, C_132, D_136)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_110])).
% 2.28/1.35  tff(c_138, plain, (![A_163, B_161, C_160, C_159, D_166, D_165, B_164, A_162]: (~r1_xboole_0(D_165, D_166) | r1_xboole_0(k4_zfmisc_1(A_163, B_164, C_160, D_165), k4_zfmisc_1(A_162, B_161, C_159, D_166)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 2.28/1.35  tff(c_141, plain, (~r1_xboole_0('#skF_4', '#skF_8')), inference(resolution, [status(thm)], [c_138, c_16])).
% 2.28/1.35  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_141])).
% 2.28/1.35  tff(c_146, plain, (r1_xboole_0('#skF_3', '#skF_7') | r1_xboole_0('#skF_2', '#skF_6')), inference(splitRight, [status(thm)], [c_100])).
% 2.28/1.35  tff(c_148, plain, (r1_xboole_0('#skF_2', '#skF_6')), inference(splitLeft, [status(thm)], [c_146])).
% 2.28/1.35  tff(c_2, plain, (![C_3, D_4, A_1, B_2]: (~r1_xboole_0(C_3, D_4) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.35  tff(c_149, plain, (![C_170, A_171, F_168, D_167, B_169, E_172]: (~r1_xboole_0(A_171, D_167) | r1_xboole_0(k3_zfmisc_1(A_171, B_169, C_170), k3_zfmisc_1(D_167, E_172, F_168)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.35  tff(c_184, plain, (![D_217, C_216, D_221, B_220, F_218, A_219, E_215]: (~r1_xboole_0(k2_zfmisc_1(A_219, B_220), D_217) | r1_xboole_0(k4_zfmisc_1(A_219, B_220, C_216, D_221), k3_zfmisc_1(D_217, E_215, F_218)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_149])).
% 2.28/1.35  tff(c_197, plain, (![C_238, D_243, B_244, A_240, B_242, A_237, C_239, D_241]: (~r1_xboole_0(k2_zfmisc_1(A_237, B_244), k2_zfmisc_1(A_240, B_242)) | r1_xboole_0(k4_zfmisc_1(A_237, B_244, C_239, D_241), k4_zfmisc_1(A_240, B_242, C_238, D_243)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_184])).
% 2.28/1.35  tff(c_201, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_197, c_16])).
% 2.28/1.35  tff(c_204, plain, (~r1_xboole_0('#skF_2', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_201])).
% 2.28/1.35  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_204])).
% 2.28/1.35  tff(c_212, plain, (r1_xboole_0('#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_146])).
% 2.28/1.35  tff(c_28, plain, (![C_30, A_31, E_32, D_27, F_28, B_29]: (~r1_xboole_0(B_29, E_32) | r1_xboole_0(k3_zfmisc_1(A_31, B_29, C_30), k3_zfmisc_1(D_27, E_32, F_28)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.35  tff(c_240, plain, (![A_279, D_284, C_278, B_283, C_280, A_281, B_282]: (~r1_xboole_0(B_283, C_278) | r1_xboole_0(k3_zfmisc_1(A_279, B_283, C_280), k4_zfmisc_1(A_281, B_282, C_278, D_284)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_28])).
% 2.28/1.35  tff(c_249, plain, (![C_296, A_293, D_299, C_294, D_300, B_298, A_297, B_295]: (~r1_xboole_0(C_294, C_296) | r1_xboole_0(k4_zfmisc_1(A_297, B_298, C_294, D_299), k4_zfmisc_1(A_293, B_295, C_296, D_300)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_240])).
% 2.28/1.35  tff(c_252, plain, (~r1_xboole_0('#skF_3', '#skF_7')), inference(resolution, [status(thm)], [c_249, c_16])).
% 2.28/1.35  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_252])).
% 2.28/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  Inference rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Ref     : 0
% 2.28/1.35  #Sup     : 54
% 2.28/1.35  #Fact    : 0
% 2.28/1.35  #Define  : 0
% 2.28/1.35  #Split   : 3
% 2.28/1.35  #Chain   : 0
% 2.28/1.35  #Close   : 0
% 2.28/1.35  
% 2.28/1.35  Ordering : KBO
% 2.28/1.35  
% 2.28/1.35  Simplification rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Subsume      : 6
% 2.28/1.35  #Demod        : 4
% 2.28/1.35  #Tautology    : 2
% 2.28/1.35  #SimpNegUnit  : 0
% 2.28/1.35  #BackRed      : 0
% 2.28/1.35  
% 2.28/1.35  #Partial instantiations: 0
% 2.28/1.35  #Strategies tried      : 1
% 2.28/1.35  
% 2.28/1.35  Timing (in seconds)
% 2.28/1.35  ----------------------
% 2.28/1.36  Preprocessing        : 0.27
% 2.28/1.36  Parsing              : 0.16
% 2.28/1.36  CNF conversion       : 0.02
% 2.28/1.36  Main loop            : 0.26
% 2.28/1.36  Inferencing          : 0.13
% 2.28/1.36  Reduction            : 0.05
% 2.28/1.36  Demodulation         : 0.03
% 2.28/1.36  BG Simplification    : 0.01
% 2.28/1.36  Subsumption          : 0.05
% 2.28/1.36  Abstraction          : 0.01
% 2.28/1.36  MUC search           : 0.00
% 2.28/1.36  Cooper               : 0.00
% 2.28/1.36  Total                : 0.56
% 2.28/1.36  Index Insertion      : 0.00
% 2.28/1.36  Index Deletion       : 0.00
% 2.28/1.36  Index Matching       : 0.00
% 2.28/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
