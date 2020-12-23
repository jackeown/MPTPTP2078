%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:38 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 103 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 ( 160 expanded)
%              Number of equality atoms :   16 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_32,plain,(
    ! [A_47] :
      ( r2_hidden('#skF_5'(A_47),A_47)
      | v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_67,B_68] : ~ r2_hidden(A_67,k2_zfmisc_1(A_67,B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_70] : ~ r2_hidden(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_276,plain,(
    ! [A_108,B_109,D_110] :
      ( r2_hidden(k4_tarski('#skF_4'(A_108,B_109,k9_relat_1(A_108,B_109),D_110),D_110),A_108)
      | ~ r2_hidden(D_110,k9_relat_1(A_108,B_109))
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_290,plain,(
    ! [D_110,B_109] :
      ( ~ r2_hidden(D_110,k9_relat_1(k1_xboole_0,B_109))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_276,c_63])).

tff(c_306,plain,(
    ! [D_111,B_112] : ~ r2_hidden(D_111,k9_relat_1(k1_xboole_0,B_112)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_290])).

tff(c_339,plain,(
    ! [B_113] : v1_relat_1(k9_relat_1(k1_xboole_0,B_113)) ),
    inference(resolution,[status(thm)],[c_32,c_306])).

tff(c_140,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden('#skF_2'(A_99,B_100,C_101),B_100)
      | r2_hidden('#skF_3'(A_99,B_100,C_101),C_101)
      | k9_relat_1(A_99,B_100) = C_101
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_175,plain,(
    ! [A_104,C_105] :
      ( r2_hidden('#skF_3'(A_104,k1_xboole_0,C_105),C_105)
      | k9_relat_1(A_104,k1_xboole_0) = C_105
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_140,c_63])).

tff(c_193,plain,(
    ! [A_104] :
      ( k9_relat_1(A_104,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_175,c_63])).

tff(c_345,plain,(
    ! [B_113] : k9_relat_1(k9_relat_1(k1_xboole_0,B_113),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_339,c_193])).

tff(c_338,plain,(
    ! [B_112] : v1_relat_1(k9_relat_1(k1_xboole_0,B_112)) ),
    inference(resolution,[status(thm)],[c_32,c_306])).

tff(c_170,plain,(
    ! [A_99,C_101] :
      ( r2_hidden('#skF_3'(A_99,k1_xboole_0,C_101),C_101)
      | k9_relat_1(A_99,k1_xboole_0) = C_101
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_140,c_63])).

tff(c_409,plain,(
    ! [B_118,A_119] :
      ( k9_relat_1(k1_xboole_0,B_118) = k9_relat_1(A_119,k1_xboole_0)
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_170,c_306])).

tff(c_411,plain,(
    ! [B_112,B_118] : k9_relat_1(k9_relat_1(k1_xboole_0,B_112),k1_xboole_0) = k9_relat_1(k1_xboole_0,B_118) ),
    inference(resolution,[status(thm)],[c_338,c_409])).

tff(c_419,plain,(
    ! [B_118] : k9_relat_1(k1_xboole_0,B_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_411])).

tff(c_34,plain,(
    k9_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.32  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_7
% 2.08/1.32  
% 2.08/1.32  %Foreground sorts:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Background operators:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Foreground operators:
% 2.08/1.32  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.08/1.32  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.08/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.08/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.08/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.08/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.32  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.08/1.32  
% 2.35/1.33  tff(f_57, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.35/1.33  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.35/1.33  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.35/1.33  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 2.35/1.33  tff(f_60, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.35/1.33  tff(c_32, plain, (![A_47]: (r2_hidden('#skF_5'(A_47), A_47) | v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.33  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.33  tff(c_57, plain, (![A_67, B_68]: (~r2_hidden(A_67, k2_zfmisc_1(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.35/1.33  tff(c_65, plain, (![A_70]: (~r2_hidden(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.35/1.33  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.35/1.33  tff(c_276, plain, (![A_108, B_109, D_110]: (r2_hidden(k4_tarski('#skF_4'(A_108, B_109, k9_relat_1(A_108, B_109), D_110), D_110), A_108) | ~r2_hidden(D_110, k9_relat_1(A_108, B_109)) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.33  tff(c_63, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.35/1.33  tff(c_290, plain, (![D_110, B_109]: (~r2_hidden(D_110, k9_relat_1(k1_xboole_0, B_109)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_276, c_63])).
% 2.35/1.33  tff(c_306, plain, (![D_111, B_112]: (~r2_hidden(D_111, k9_relat_1(k1_xboole_0, B_112)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_290])).
% 2.35/1.33  tff(c_339, plain, (![B_113]: (v1_relat_1(k9_relat_1(k1_xboole_0, B_113)))), inference(resolution, [status(thm)], [c_32, c_306])).
% 2.35/1.33  tff(c_140, plain, (![A_99, B_100, C_101]: (r2_hidden('#skF_2'(A_99, B_100, C_101), B_100) | r2_hidden('#skF_3'(A_99, B_100, C_101), C_101) | k9_relat_1(A_99, B_100)=C_101 | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.35/1.33  tff(c_175, plain, (![A_104, C_105]: (r2_hidden('#skF_3'(A_104, k1_xboole_0, C_105), C_105) | k9_relat_1(A_104, k1_xboole_0)=C_105 | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_140, c_63])).
% 2.35/1.33  tff(c_193, plain, (![A_104]: (k9_relat_1(A_104, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_175, c_63])).
% 2.35/1.33  tff(c_345, plain, (![B_113]: (k9_relat_1(k9_relat_1(k1_xboole_0, B_113), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_339, c_193])).
% 2.35/1.33  tff(c_338, plain, (![B_112]: (v1_relat_1(k9_relat_1(k1_xboole_0, B_112)))), inference(resolution, [status(thm)], [c_32, c_306])).
% 2.35/1.33  tff(c_170, plain, (![A_99, C_101]: (r2_hidden('#skF_3'(A_99, k1_xboole_0, C_101), C_101) | k9_relat_1(A_99, k1_xboole_0)=C_101 | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_140, c_63])).
% 2.35/1.33  tff(c_409, plain, (![B_118, A_119]: (k9_relat_1(k1_xboole_0, B_118)=k9_relat_1(A_119, k1_xboole_0) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_170, c_306])).
% 2.35/1.33  tff(c_411, plain, (![B_112, B_118]: (k9_relat_1(k9_relat_1(k1_xboole_0, B_112), k1_xboole_0)=k9_relat_1(k1_xboole_0, B_118))), inference(resolution, [status(thm)], [c_338, c_409])).
% 2.35/1.33  tff(c_419, plain, (![B_118]: (k9_relat_1(k1_xboole_0, B_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_411])).
% 2.35/1.33  tff(c_34, plain, (k9_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.33  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_419, c_34])).
% 2.35/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  Inference rules
% 2.35/1.33  ----------------------
% 2.35/1.33  #Ref     : 1
% 2.35/1.33  #Sup     : 84
% 2.35/1.33  #Fact    : 0
% 2.35/1.33  #Define  : 0
% 2.35/1.33  #Split   : 0
% 2.35/1.33  #Chain   : 0
% 2.35/1.33  #Close   : 0
% 2.35/1.33  
% 2.35/1.33  Ordering : KBO
% 2.35/1.33  
% 2.35/1.33  Simplification rules
% 2.35/1.33  ----------------------
% 2.35/1.33  #Subsume      : 19
% 2.35/1.33  #Demod        : 40
% 2.35/1.33  #Tautology    : 31
% 2.35/1.33  #SimpNegUnit  : 5
% 2.35/1.33  #BackRed      : 4
% 2.35/1.33  
% 2.35/1.33  #Partial instantiations: 0
% 2.35/1.33  #Strategies tried      : 1
% 2.35/1.33  
% 2.35/1.33  Timing (in seconds)
% 2.35/1.33  ----------------------
% 2.35/1.33  Preprocessing        : 0.29
% 2.35/1.33  Parsing              : 0.15
% 2.35/1.33  CNF conversion       : 0.03
% 2.35/1.33  Main loop            : 0.26
% 2.35/1.33  Inferencing          : 0.10
% 2.35/1.33  Reduction            : 0.07
% 2.35/1.33  Demodulation         : 0.05
% 2.35/1.33  BG Simplification    : 0.02
% 2.35/1.33  Subsumption          : 0.06
% 2.35/1.33  Abstraction          : 0.01
% 2.35/1.33  MUC search           : 0.00
% 2.35/1.33  Cooper               : 0.00
% 2.35/1.33  Total                : 0.59
% 2.35/1.33  Index Insertion      : 0.00
% 2.35/1.33  Index Deletion       : 0.00
% 2.35/1.33  Index Matching       : 0.00
% 2.35/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
