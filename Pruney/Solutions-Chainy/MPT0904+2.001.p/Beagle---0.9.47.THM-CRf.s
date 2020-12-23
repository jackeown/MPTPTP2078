%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 113 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 191 expanded)
%              Number of equality atoms :    5 (  28 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( ~ r1_xboole_0(k4_zfmisc_1(A,B,C,D),k4_zfmisc_1(E,F,G,H))
       => ( ~ r1_xboole_0(A,E)
          & ~ r1_xboole_0(B,F)
          & ~ r1_xboole_0(C,G)
          & ~ r1_xboole_0(D,H) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(c_10,plain,
    ( r1_xboole_0('#skF_4','#skF_8')
    | r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_2','#skF_6')
    | r1_xboole_0('#skF_1','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    r1_xboole_0('#skF_1','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( ~ r1_xboole_0(A_15,B_16)
      | r1_xboole_0(k2_zfmisc_1(A_15,C_17),k2_zfmisc_1(B_16,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [D_59,C_62,A_63,B_61,B_60] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_63,B_61),B_60)
      | r1_xboole_0(k3_zfmisc_1(A_63,B_61,C_62),k2_zfmisc_1(B_60,D_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_137,plain,(
    ! [B_6,C_7,C_62,A_5,A_63,B_61] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_63,B_61),k2_zfmisc_1(A_5,B_6))
      | r1_xboole_0(k3_zfmisc_1(A_63,B_61,C_62),k3_zfmisc_1(A_5,B_6,C_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_128])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_zfmisc_1(k3_zfmisc_1(A_23,B_24,C_25),D_26) = k4_zfmisc_1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    ! [D_91,B_92,B_89,A_93,C_88,D_90] :
      ( ~ r1_xboole_0(k3_zfmisc_1(A_93,B_89,C_88),B_92)
      | r1_xboole_0(k4_zfmisc_1(A_93,B_89,C_88,D_90),k2_zfmisc_1(B_92,D_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_371,plain,(
    ! [B_144,A_141,B_143,C_145,D_146,D_139,C_142,A_140] :
      ( ~ r1_xboole_0(k3_zfmisc_1(A_141,B_143,C_142),k3_zfmisc_1(A_140,B_144,C_145))
      | r1_xboole_0(k4_zfmisc_1(A_141,B_143,C_142,D_139),k4_zfmisc_1(A_140,B_144,C_145,D_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_208])).

tff(c_12,plain,(
    ~ r1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_387,plain,(
    ~ r1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_371,c_12])).

tff(c_398,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_137,c_387])).

tff(c_405,plain,(
    ~ r1_xboole_0('#skF_1','#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_398])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_405])).

tff(c_411,plain,
    ( r1_xboole_0('#skF_2','#skF_6')
    | r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_413,plain,(
    r1_xboole_0('#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_2,plain,(
    ! [C_3,D_4,A_1,B_2] :
      ( ~ r1_xboole_0(C_3,D_4)
      | r1_xboole_0(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_461,plain,(
    ! [D_170,D_169,C_167,A_172,B_168,B_171] :
      ( ~ r1_xboole_0(D_169,D_170)
      | r1_xboole_0(k4_zfmisc_1(A_172,B_168,C_167,D_169),k2_zfmisc_1(B_171,D_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_555,plain,(
    ! [B_212,B_211,A_213,D_215,A_209,D_210,C_214,C_208] :
      ( ~ r1_xboole_0(D_210,D_215)
      | r1_xboole_0(k4_zfmisc_1(A_213,B_211,C_208,D_210),k4_zfmisc_1(A_209,B_212,C_214,D_215)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_461])).

tff(c_558,plain,(
    ~ r1_xboole_0('#skF_4','#skF_8') ),
    inference(resolution,[status(thm)],[c_555,c_12])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_558])).

tff(c_563,plain,
    ( r1_xboole_0('#skF_3','#skF_7')
    | r1_xboole_0('#skF_2','#skF_6') ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_565,plain,(
    r1_xboole_0('#skF_2','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_638,plain,(
    ! [D_253,A_257,C_256,B_255,B_254] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_257,B_255),B_254)
      | r1_xboole_0(k3_zfmisc_1(A_257,B_255,C_256),k2_zfmisc_1(B_254,D_253)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_647,plain,(
    ! [B_6,C_7,A_257,C_256,B_255,A_5] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_257,B_255),k2_zfmisc_1(A_5,B_6))
      | r1_xboole_0(k3_zfmisc_1(A_257,B_255,C_256),k3_zfmisc_1(A_5,B_6,C_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_638])).

tff(c_747,plain,(
    ! [C_290,B_291,A_295,D_293,B_294,D_292] :
      ( ~ r1_xboole_0(k3_zfmisc_1(A_295,B_291,C_290),B_294)
      | r1_xboole_0(k4_zfmisc_1(A_295,B_291,C_290,D_292),k2_zfmisc_1(B_294,D_293)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_869,plain,(
    ! [C_334,D_335,B_330,A_329,A_331,D_333,C_328,B_332] :
      ( ~ r1_xboole_0(k3_zfmisc_1(A_329,B_330,C_328),k3_zfmisc_1(A_331,B_332,C_334))
      | r1_xboole_0(k4_zfmisc_1(A_329,B_330,C_328,D_333),k4_zfmisc_1(A_331,B_332,C_334,D_335)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_747])).

tff(c_885,plain,(
    ~ r1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_869,c_12])).

tff(c_896,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_647,c_885])).

tff(c_900,plain,(
    ~ r1_xboole_0('#skF_2','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_896])).

tff(c_907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_900])).

tff(c_908,plain,(
    r1_xboole_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_35,plain,(
    ! [C_19,D_20,A_21,B_22] :
      ( ~ r1_xboole_0(C_19,D_20)
      | r1_xboole_0(k2_zfmisc_1(A_21,C_19),k2_zfmisc_1(B_22,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_910,plain,(
    ! [B_338,C_339,D_336,B_337,A_340] :
      ( ~ r1_xboole_0(C_339,D_336)
      | r1_xboole_0(k3_zfmisc_1(A_340,B_337,C_339),k2_zfmisc_1(B_338,D_336)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_916,plain,(
    ! [B_6,C_7,C_339,A_5,B_337,A_340] :
      ( ~ r1_xboole_0(C_339,C_7)
      | r1_xboole_0(k3_zfmisc_1(A_340,B_337,C_339),k3_zfmisc_1(A_5,B_6,C_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_910])).

tff(c_1091,plain,(
    ! [C_410,C_413,A_415,B_411,A_414,D_412] :
      ( ~ r1_xboole_0(A_414,k3_zfmisc_1(A_415,B_411,C_410))
      | r1_xboole_0(k2_zfmisc_1(A_414,C_413),k4_zfmisc_1(A_415,B_411,C_410,D_412)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_1213,plain,(
    ! [C_454,B_453,D_455,A_448,B_450,C_452,A_451,D_449] :
      ( ~ r1_xboole_0(k3_zfmisc_1(A_448,B_453,C_454),k3_zfmisc_1(A_451,B_450,C_452))
      | r1_xboole_0(k4_zfmisc_1(A_448,B_453,C_454,D_455),k4_zfmisc_1(A_451,B_450,C_452,D_449)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1091])).

tff(c_1229,plain,(
    ~ r1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1213,c_12])).

tff(c_1239,plain,(
    ~ r1_xboole_0('#skF_3','#skF_7') ),
    inference(resolution,[status(thm)],[c_916,c_1229])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_1239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:37:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.55  
% 3.39/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.56  %$ r1_xboole_0 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.39/1.56  
% 3.39/1.56  %Foreground sorts:
% 3.39/1.56  
% 3.39/1.56  
% 3.39/1.56  %Background operators:
% 3.39/1.56  
% 3.39/1.56  
% 3.39/1.56  %Foreground operators:
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.56  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.39/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.39/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.39/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.39/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.56  
% 3.39/1.57  tff(f_51, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (~r1_xboole_0(k4_zfmisc_1(A, B, C, D), k4_zfmisc_1(E, F, G, H)) => (((~r1_xboole_0(A, E) & ~r1_xboole_0(B, F)) & ~r1_xboole_0(C, G)) & ~r1_xboole_0(D, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_mcart_1)).
% 3.39/1.57  tff(f_31, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.39/1.57  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.39/1.57  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.39/1.57  tff(c_10, plain, (r1_xboole_0('#skF_4', '#skF_8') | r1_xboole_0('#skF_3', '#skF_7') | r1_xboole_0('#skF_2', '#skF_6') | r1_xboole_0('#skF_1', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.57  tff(c_66, plain, (r1_xboole_0('#skF_1', '#skF_5')), inference(splitLeft, [status(thm)], [c_10])).
% 3.39/1.57  tff(c_4, plain, (![A_1, B_2, C_3, D_4]: (~r1_xboole_0(A_1, B_2) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.57  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.57  tff(c_28, plain, (![A_15, B_16, C_17, D_18]: (~r1_xboole_0(A_15, B_16) | r1_xboole_0(k2_zfmisc_1(A_15, C_17), k2_zfmisc_1(B_16, D_18)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.57  tff(c_128, plain, (![D_59, C_62, A_63, B_61, B_60]: (~r1_xboole_0(k2_zfmisc_1(A_63, B_61), B_60) | r1_xboole_0(k3_zfmisc_1(A_63, B_61, C_62), k2_zfmisc_1(B_60, D_59)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_28])).
% 3.39/1.57  tff(c_137, plain, (![B_6, C_7, C_62, A_5, A_63, B_61]: (~r1_xboole_0(k2_zfmisc_1(A_63, B_61), k2_zfmisc_1(A_5, B_6)) | r1_xboole_0(k3_zfmisc_1(A_63, B_61, C_62), k3_zfmisc_1(A_5, B_6, C_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_128])).
% 3.39/1.57  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.57  tff(c_42, plain, (![A_23, B_24, C_25, D_26]: (k2_zfmisc_1(k3_zfmisc_1(A_23, B_24, C_25), D_26)=k4_zfmisc_1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.57  tff(c_208, plain, (![D_91, B_92, B_89, A_93, C_88, D_90]: (~r1_xboole_0(k3_zfmisc_1(A_93, B_89, C_88), B_92) | r1_xboole_0(k4_zfmisc_1(A_93, B_89, C_88, D_90), k2_zfmisc_1(B_92, D_91)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 3.39/1.57  tff(c_371, plain, (![B_144, A_141, B_143, C_145, D_146, D_139, C_142, A_140]: (~r1_xboole_0(k3_zfmisc_1(A_141, B_143, C_142), k3_zfmisc_1(A_140, B_144, C_145)) | r1_xboole_0(k4_zfmisc_1(A_141, B_143, C_142, D_139), k4_zfmisc_1(A_140, B_144, C_145, D_146)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_208])).
% 3.39/1.57  tff(c_12, plain, (~r1_xboole_0(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.57  tff(c_387, plain, (~r1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_371, c_12])).
% 3.39/1.57  tff(c_398, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_137, c_387])).
% 3.39/1.57  tff(c_405, plain, (~r1_xboole_0('#skF_1', '#skF_5')), inference(resolution, [status(thm)], [c_4, c_398])).
% 3.39/1.57  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_405])).
% 3.39/1.57  tff(c_411, plain, (r1_xboole_0('#skF_2', '#skF_6') | r1_xboole_0('#skF_3', '#skF_7') | r1_xboole_0('#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_10])).
% 3.39/1.57  tff(c_413, plain, (r1_xboole_0('#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_411])).
% 3.39/1.57  tff(c_2, plain, (![C_3, D_4, A_1, B_2]: (~r1_xboole_0(C_3, D_4) | r1_xboole_0(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.57  tff(c_461, plain, (![D_170, D_169, C_167, A_172, B_168, B_171]: (~r1_xboole_0(D_169, D_170) | r1_xboole_0(k4_zfmisc_1(A_172, B_168, C_167, D_169), k2_zfmisc_1(B_171, D_170)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 3.39/1.57  tff(c_555, plain, (![B_212, B_211, A_213, D_215, A_209, D_210, C_214, C_208]: (~r1_xboole_0(D_210, D_215) | r1_xboole_0(k4_zfmisc_1(A_213, B_211, C_208, D_210), k4_zfmisc_1(A_209, B_212, C_214, D_215)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_461])).
% 3.39/1.57  tff(c_558, plain, (~r1_xboole_0('#skF_4', '#skF_8')), inference(resolution, [status(thm)], [c_555, c_12])).
% 3.39/1.57  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_413, c_558])).
% 3.39/1.57  tff(c_563, plain, (r1_xboole_0('#skF_3', '#skF_7') | r1_xboole_0('#skF_2', '#skF_6')), inference(splitRight, [status(thm)], [c_411])).
% 3.39/1.57  tff(c_565, plain, (r1_xboole_0('#skF_2', '#skF_6')), inference(splitLeft, [status(thm)], [c_563])).
% 3.39/1.57  tff(c_638, plain, (![D_253, A_257, C_256, B_255, B_254]: (~r1_xboole_0(k2_zfmisc_1(A_257, B_255), B_254) | r1_xboole_0(k3_zfmisc_1(A_257, B_255, C_256), k2_zfmisc_1(B_254, D_253)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_28])).
% 3.39/1.57  tff(c_647, plain, (![B_6, C_7, A_257, C_256, B_255, A_5]: (~r1_xboole_0(k2_zfmisc_1(A_257, B_255), k2_zfmisc_1(A_5, B_6)) | r1_xboole_0(k3_zfmisc_1(A_257, B_255, C_256), k3_zfmisc_1(A_5, B_6, C_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_638])).
% 3.39/1.57  tff(c_747, plain, (![C_290, B_291, A_295, D_293, B_294, D_292]: (~r1_xboole_0(k3_zfmisc_1(A_295, B_291, C_290), B_294) | r1_xboole_0(k4_zfmisc_1(A_295, B_291, C_290, D_292), k2_zfmisc_1(B_294, D_293)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 3.39/1.57  tff(c_869, plain, (![C_334, D_335, B_330, A_329, A_331, D_333, C_328, B_332]: (~r1_xboole_0(k3_zfmisc_1(A_329, B_330, C_328), k3_zfmisc_1(A_331, B_332, C_334)) | r1_xboole_0(k4_zfmisc_1(A_329, B_330, C_328, D_333), k4_zfmisc_1(A_331, B_332, C_334, D_335)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_747])).
% 3.39/1.57  tff(c_885, plain, (~r1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_869, c_12])).
% 3.39/1.57  tff(c_896, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_647, c_885])).
% 3.39/1.57  tff(c_900, plain, (~r1_xboole_0('#skF_2', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_896])).
% 3.39/1.57  tff(c_907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_565, c_900])).
% 3.39/1.57  tff(c_908, plain, (r1_xboole_0('#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_563])).
% 3.39/1.57  tff(c_35, plain, (![C_19, D_20, A_21, B_22]: (~r1_xboole_0(C_19, D_20) | r1_xboole_0(k2_zfmisc_1(A_21, C_19), k2_zfmisc_1(B_22, D_20)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.57  tff(c_910, plain, (![B_338, C_339, D_336, B_337, A_340]: (~r1_xboole_0(C_339, D_336) | r1_xboole_0(k3_zfmisc_1(A_340, B_337, C_339), k2_zfmisc_1(B_338, D_336)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_35])).
% 3.39/1.57  tff(c_916, plain, (![B_6, C_7, C_339, A_5, B_337, A_340]: (~r1_xboole_0(C_339, C_7) | r1_xboole_0(k3_zfmisc_1(A_340, B_337, C_339), k3_zfmisc_1(A_5, B_6, C_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_910])).
% 3.39/1.57  tff(c_1091, plain, (![C_410, C_413, A_415, B_411, A_414, D_412]: (~r1_xboole_0(A_414, k3_zfmisc_1(A_415, B_411, C_410)) | r1_xboole_0(k2_zfmisc_1(A_414, C_413), k4_zfmisc_1(A_415, B_411, C_410, D_412)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 3.39/1.57  tff(c_1213, plain, (![C_454, B_453, D_455, A_448, B_450, C_452, A_451, D_449]: (~r1_xboole_0(k3_zfmisc_1(A_448, B_453, C_454), k3_zfmisc_1(A_451, B_450, C_452)) | r1_xboole_0(k4_zfmisc_1(A_448, B_453, C_454, D_455), k4_zfmisc_1(A_451, B_450, C_452, D_449)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1091])).
% 3.39/1.57  tff(c_1229, plain, (~r1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1213, c_12])).
% 3.39/1.57  tff(c_1239, plain, (~r1_xboole_0('#skF_3', '#skF_7')), inference(resolution, [status(thm)], [c_916, c_1229])).
% 3.39/1.57  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_908, c_1239])).
% 3.39/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.57  
% 3.39/1.57  Inference rules
% 3.39/1.57  ----------------------
% 3.39/1.57  #Ref     : 0
% 3.39/1.57  #Sup     : 320
% 3.39/1.57  #Fact    : 0
% 3.39/1.57  #Define  : 0
% 3.39/1.57  #Split   : 3
% 3.39/1.57  #Chain   : 0
% 3.39/1.57  #Close   : 0
% 3.39/1.57  
% 3.39/1.57  Ordering : KBO
% 3.39/1.57  
% 3.39/1.57  Simplification rules
% 3.39/1.57  ----------------------
% 3.39/1.57  #Subsume      : 177
% 3.39/1.57  #Demod        : 161
% 3.39/1.57  #Tautology    : 63
% 3.39/1.57  #SimpNegUnit  : 0
% 3.39/1.57  #BackRed      : 0
% 3.39/1.57  
% 3.39/1.57  #Partial instantiations: 0
% 3.39/1.57  #Strategies tried      : 1
% 3.39/1.57  
% 3.39/1.57  Timing (in seconds)
% 3.39/1.57  ----------------------
% 3.39/1.58  Preprocessing        : 0.27
% 3.39/1.58  Parsing              : 0.15
% 3.39/1.58  CNF conversion       : 0.02
% 3.39/1.58  Main loop            : 0.53
% 3.39/1.58  Inferencing          : 0.24
% 3.39/1.58  Reduction            : 0.14
% 3.39/1.58  Demodulation         : 0.10
% 3.39/1.58  BG Simplification    : 0.02
% 3.39/1.58  Subsumption          : 0.10
% 3.39/1.58  Abstraction          : 0.03
% 3.39/1.58  MUC search           : 0.00
% 3.39/1.58  Cooper               : 0.00
% 3.39/1.58  Total                : 0.84
% 3.39/1.58  Index Insertion      : 0.00
% 3.39/1.58  Index Deletion       : 0.00
% 3.39/1.58  Index Matching       : 0.00
% 3.39/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
