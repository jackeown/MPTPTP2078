%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 136 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 271 expanded)
%              Number of equality atoms :   16 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_64,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_330,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( r2_hidden(k4_tarski(A_115,B_116),k2_zfmisc_1(C_117,D_118))
      | ~ r2_hidden(B_116,D_118)
      | ~ r2_hidden(A_115,C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_142,plain,(
    ! [A_67,C_68,B_69,D_70] :
      ( r2_hidden(A_67,C_68)
      | ~ r2_hidden(k4_tarski(A_67,B_69),k2_zfmisc_1(C_68,D_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_145,plain,(
    ! [A_67,B_69] :
      ( r2_hidden(A_67,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_67,B_69),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_142])).

tff(c_356,plain,(
    ! [A_115,B_116] :
      ( r2_hidden(A_115,'#skF_9')
      | ~ r2_hidden(B_116,'#skF_9')
      | ~ r2_hidden(A_115,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_330,c_145])).

tff(c_363,plain,(
    ! [B_119] : ~ r2_hidden(B_119,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_374,plain,(
    ! [B_120] : r1_tarski('#skF_9',B_120) ),
    inference(resolution,[status(thm)],[c_6,c_363])).

tff(c_26,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_167,plain,(
    ! [A_87,C_88,B_89] :
      ( ~ r2_hidden(A_87,C_88)
      | ~ r2_hidden(A_87,B_89)
      | ~ r2_hidden(A_87,k5_xboole_0(B_89,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_176,plain,(
    ! [A_90,A_91] :
      ( ~ r2_hidden(A_90,k1_xboole_0)
      | ~ r2_hidden(A_90,A_91)
      | ~ r2_hidden(A_90,A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_167])).

tff(c_181,plain,(
    ! [B_92,A_93] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_92),A_93)
      | r1_tarski(k1_xboole_0,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_209,plain,(
    ! [B_97] : r1_tarski(k1_xboole_0,B_97) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_212,plain,(
    ! [B_97] :
      ( k1_xboole_0 = B_97
      | ~ r1_tarski(B_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_209,c_20])).

tff(c_381,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_374,c_212])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_381])).

tff(c_411,plain,(
    ! [A_123] :
      ( r2_hidden(A_123,'#skF_9')
      | ~ r2_hidden(A_123,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_420,plain,(
    ! [A_124] :
      ( r1_tarski(A_124,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_124,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_411,c_4])).

tff(c_430,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_420])).

tff(c_432,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_430,c_20])).

tff(c_435,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_432])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_152,plain,(
    ! [B_71,D_72,A_73,C_74] :
      ( r2_hidden(B_71,D_72)
      | ~ r2_hidden(k4_tarski(A_73,B_71),k2_zfmisc_1(C_74,D_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_155,plain,(
    ! [B_71,A_73] :
      ( r2_hidden(B_71,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_73,B_71),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_152])).

tff(c_357,plain,(
    ! [B_116,A_115] :
      ( r2_hidden(B_116,'#skF_8')
      | ~ r2_hidden(B_116,'#skF_9')
      | ~ r2_hidden(A_115,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_330,c_155])).

tff(c_487,plain,(
    ! [A_130] : ~ r2_hidden(A_130,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_510,plain,(
    ! [B_133] : r1_tarski('#skF_8',B_133) ),
    inference(resolution,[status(thm)],[c_6,c_487])).

tff(c_517,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_510,c_212])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_517])).

tff(c_527,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,'#skF_8')
      | ~ r2_hidden(B_134,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_547,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_1'('#skF_9',B_135),'#skF_8')
      | r1_tarski('#skF_9',B_135) ) ),
    inference(resolution,[status(thm)],[c_6,c_527])).

tff(c_557,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_547,c_4])).

tff(c_564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_435,c_557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.50  
% 2.75/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.50  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 2.89/1.50  
% 2.89/1.50  %Foreground sorts:
% 2.89/1.50  
% 2.89/1.50  
% 2.89/1.50  %Background operators:
% 2.89/1.50  
% 2.89/1.50  
% 2.89/1.50  %Foreground operators:
% 2.89/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.89/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.89/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.89/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.89/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.89/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.89/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.89/1.50  tff('#skF_9', type, '#skF_9': $i).
% 2.89/1.50  tff('#skF_8', type, '#skF_8': $i).
% 2.89/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.89/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.50  
% 2.89/1.52  tff(f_80, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.89/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.89/1.52  tff(f_65, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.89/1.52  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.89/1.52  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.89/1.52  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.89/1.52  tff(c_64, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.89/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.89/1.52  tff(c_66, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.89/1.52  tff(c_330, plain, (![A_115, B_116, C_117, D_118]: (r2_hidden(k4_tarski(A_115, B_116), k2_zfmisc_1(C_117, D_118)) | ~r2_hidden(B_116, D_118) | ~r2_hidden(A_115, C_117))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.52  tff(c_70, plain, (k2_zfmisc_1('#skF_9', '#skF_8')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.89/1.52  tff(c_142, plain, (![A_67, C_68, B_69, D_70]: (r2_hidden(A_67, C_68) | ~r2_hidden(k4_tarski(A_67, B_69), k2_zfmisc_1(C_68, D_70)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.52  tff(c_145, plain, (![A_67, B_69]: (r2_hidden(A_67, '#skF_9') | ~r2_hidden(k4_tarski(A_67, B_69), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_142])).
% 2.89/1.52  tff(c_356, plain, (![A_115, B_116]: (r2_hidden(A_115, '#skF_9') | ~r2_hidden(B_116, '#skF_9') | ~r2_hidden(A_115, '#skF_8'))), inference(resolution, [status(thm)], [c_330, c_145])).
% 2.89/1.52  tff(c_363, plain, (![B_119]: (~r2_hidden(B_119, '#skF_9'))), inference(splitLeft, [status(thm)], [c_356])).
% 2.89/1.52  tff(c_374, plain, (![B_120]: (r1_tarski('#skF_9', B_120))), inference(resolution, [status(thm)], [c_6, c_363])).
% 2.89/1.52  tff(c_26, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.52  tff(c_167, plain, (![A_87, C_88, B_89]: (~r2_hidden(A_87, C_88) | ~r2_hidden(A_87, B_89) | ~r2_hidden(A_87, k5_xboole_0(B_89, C_88)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.52  tff(c_176, plain, (![A_90, A_91]: (~r2_hidden(A_90, k1_xboole_0) | ~r2_hidden(A_90, A_91) | ~r2_hidden(A_90, A_91))), inference(superposition, [status(thm), theory('equality')], [c_26, c_167])).
% 2.89/1.52  tff(c_181, plain, (![B_92, A_93]: (~r2_hidden('#skF_1'(k1_xboole_0, B_92), A_93) | r1_tarski(k1_xboole_0, B_92))), inference(resolution, [status(thm)], [c_6, c_176])).
% 2.89/1.52  tff(c_209, plain, (![B_97]: (r1_tarski(k1_xboole_0, B_97))), inference(resolution, [status(thm)], [c_6, c_181])).
% 2.89/1.52  tff(c_20, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.52  tff(c_212, plain, (![B_97]: (k1_xboole_0=B_97 | ~r1_tarski(B_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_209, c_20])).
% 2.89/1.52  tff(c_381, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_374, c_212])).
% 2.89/1.52  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_381])).
% 2.89/1.52  tff(c_411, plain, (![A_123]: (r2_hidden(A_123, '#skF_9') | ~r2_hidden(A_123, '#skF_8'))), inference(splitRight, [status(thm)], [c_356])).
% 2.89/1.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.89/1.52  tff(c_420, plain, (![A_124]: (r1_tarski(A_124, '#skF_9') | ~r2_hidden('#skF_1'(A_124, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_411, c_4])).
% 2.89/1.52  tff(c_430, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_6, c_420])).
% 2.89/1.52  tff(c_432, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_430, c_20])).
% 2.89/1.52  tff(c_435, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_432])).
% 2.89/1.52  tff(c_68, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.89/1.52  tff(c_152, plain, (![B_71, D_72, A_73, C_74]: (r2_hidden(B_71, D_72) | ~r2_hidden(k4_tarski(A_73, B_71), k2_zfmisc_1(C_74, D_72)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.52  tff(c_155, plain, (![B_71, A_73]: (r2_hidden(B_71, '#skF_8') | ~r2_hidden(k4_tarski(A_73, B_71), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_152])).
% 2.89/1.52  tff(c_357, plain, (![B_116, A_115]: (r2_hidden(B_116, '#skF_8') | ~r2_hidden(B_116, '#skF_9') | ~r2_hidden(A_115, '#skF_8'))), inference(resolution, [status(thm)], [c_330, c_155])).
% 2.89/1.52  tff(c_487, plain, (![A_130]: (~r2_hidden(A_130, '#skF_8'))), inference(splitLeft, [status(thm)], [c_357])).
% 2.89/1.52  tff(c_510, plain, (![B_133]: (r1_tarski('#skF_8', B_133))), inference(resolution, [status(thm)], [c_6, c_487])).
% 2.89/1.52  tff(c_517, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_510, c_212])).
% 2.89/1.52  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_517])).
% 2.89/1.52  tff(c_527, plain, (![B_134]: (r2_hidden(B_134, '#skF_8') | ~r2_hidden(B_134, '#skF_9'))), inference(splitRight, [status(thm)], [c_357])).
% 2.89/1.52  tff(c_547, plain, (![B_135]: (r2_hidden('#skF_1'('#skF_9', B_135), '#skF_8') | r1_tarski('#skF_9', B_135))), inference(resolution, [status(thm)], [c_6, c_527])).
% 2.89/1.52  tff(c_557, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_547, c_4])).
% 2.89/1.52  tff(c_564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_435, c_557])).
% 2.89/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.52  
% 2.89/1.52  Inference rules
% 2.89/1.52  ----------------------
% 2.89/1.52  #Ref     : 0
% 2.89/1.52  #Sup     : 105
% 2.89/1.52  #Fact    : 0
% 2.89/1.52  #Define  : 0
% 2.89/1.52  #Split   : 2
% 2.89/1.52  #Chain   : 0
% 2.89/1.52  #Close   : 0
% 2.89/1.52  
% 2.89/1.52  Ordering : KBO
% 2.89/1.52  
% 2.89/1.52  Simplification rules
% 2.89/1.52  ----------------------
% 2.89/1.52  #Subsume      : 16
% 2.89/1.52  #Demod        : 18
% 2.89/1.52  #Tautology    : 39
% 2.89/1.52  #SimpNegUnit  : 7
% 2.89/1.52  #BackRed      : 2
% 2.89/1.52  
% 2.89/1.52  #Partial instantiations: 0
% 2.89/1.52  #Strategies tried      : 1
% 2.89/1.52  
% 2.89/1.52  Timing (in seconds)
% 2.89/1.52  ----------------------
% 2.89/1.52  Preprocessing        : 0.35
% 2.89/1.52  Parsing              : 0.17
% 2.89/1.52  CNF conversion       : 0.03
% 2.89/1.52  Main loop            : 0.31
% 2.89/1.52  Inferencing          : 0.11
% 2.89/1.52  Reduction            : 0.08
% 2.89/1.52  Demodulation         : 0.06
% 2.89/1.52  BG Simplification    : 0.02
% 2.89/1.52  Subsumption          : 0.08
% 2.89/1.52  Abstraction          : 0.01
% 2.89/1.52  MUC search           : 0.00
% 2.89/1.52  Cooper               : 0.00
% 2.89/1.52  Total                : 0.70
% 2.89/1.52  Index Insertion      : 0.00
% 2.89/1.52  Index Deletion       : 0.00
% 2.89/1.52  Index Matching       : 0.00
% 2.89/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
