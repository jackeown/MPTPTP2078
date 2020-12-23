%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 170 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 342 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( r2_hidden(k4_tarski(A_109,B_110),k2_zfmisc_1(C_111,D_112))
      | ~ r2_hidden(B_110,D_112)
      | ~ r2_hidden(A_109,C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    k2_zfmisc_1('#skF_10','#skF_9') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_190,plain,(
    ! [B_87,D_88,A_89,C_90] :
      ( r2_hidden(B_87,D_88)
      | ~ r2_hidden(k4_tarski(A_89,B_87),k2_zfmisc_1(C_90,D_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_193,plain,(
    ! [B_87,A_89] :
      ( r2_hidden(B_87,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_89,B_87),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_190])).

tff(c_260,plain,(
    ! [B_110,A_109] :
      ( r2_hidden(B_110,'#skF_9')
      | ~ r2_hidden(B_110,'#skF_10')
      | ~ r2_hidden(A_109,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_231,c_193])).

tff(c_288,plain,(
    ! [A_116] : ~ r2_hidden(A_116,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_313,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_2'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_60,B_61] :
      ( ~ v1_xboole_0(A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_125,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_108,c_125])).

tff(c_145,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ v1_xboole_0(B_70)
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_108,c_135])).

tff(c_148,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_316,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_313,c_148])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_316])).

tff(c_324,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,'#skF_9')
      | ~ r2_hidden(B_117,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_987,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_2'('#skF_10',B_166),'#skF_9')
      | r1_tarski('#skF_10',B_166) ) ),
    inference(resolution,[status(thm)],[c_10,c_324])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_998,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_987,c_8])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1060,plain,
    ( '#skF_10' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_998,c_14])).

tff(c_1069,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1060])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_344,plain,
    ( r2_hidden('#skF_1'('#skF_10'),'#skF_9')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_324])).

tff(c_369,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_372,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_369,c_148])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_372])).

tff(c_380,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_179,plain,(
    ! [A_80,C_81,B_82,D_83] :
      ( r2_hidden(A_80,C_81)
      | ~ r2_hidden(k4_tarski(A_80,B_82),k2_zfmisc_1(C_81,D_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_182,plain,(
    ! [A_80,B_82] :
      ( r2_hidden(A_80,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_80,B_82),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_179])).

tff(c_261,plain,(
    ! [A_109,B_110] :
      ( r2_hidden(A_109,'#skF_10')
      | ~ r2_hidden(B_110,'#skF_10')
      | ~ r2_hidden(A_109,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_231,c_182])).

tff(c_508,plain,(
    ! [B_128] : ~ r2_hidden(B_128,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_528,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_508])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_528])).

tff(c_631,plain,(
    ! [A_136] :
      ( r2_hidden(A_136,'#skF_10')
      | ~ r2_hidden(A_136,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_1096,plain,(
    ! [A_174] :
      ( r1_tarski(A_174,'#skF_10')
      | ~ r2_hidden('#skF_2'(A_174,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_631,c_8])).

tff(c_1108,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_1096])).

tff(c_1115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1069,c_1069,c_1108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.69/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.69/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.69/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.41  tff('#skF_10', type, '#skF_10': $i).
% 2.69/1.41  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.41  
% 2.69/1.42  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.69/1.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.69/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.69/1.42  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.69/1.42  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.42  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.42  tff(c_56, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.42  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.42  tff(c_60, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.42  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.42  tff(c_231, plain, (![A_109, B_110, C_111, D_112]: (r2_hidden(k4_tarski(A_109, B_110), k2_zfmisc_1(C_111, D_112)) | ~r2_hidden(B_110, D_112) | ~r2_hidden(A_109, C_111))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.42  tff(c_62, plain, (k2_zfmisc_1('#skF_10', '#skF_9')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.42  tff(c_190, plain, (![B_87, D_88, A_89, C_90]: (r2_hidden(B_87, D_88) | ~r2_hidden(k4_tarski(A_89, B_87), k2_zfmisc_1(C_90, D_88)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.42  tff(c_193, plain, (![B_87, A_89]: (r2_hidden(B_87, '#skF_9') | ~r2_hidden(k4_tarski(A_89, B_87), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_190])).
% 2.69/1.42  tff(c_260, plain, (![B_110, A_109]: (r2_hidden(B_110, '#skF_9') | ~r2_hidden(B_110, '#skF_10') | ~r2_hidden(A_109, '#skF_9'))), inference(resolution, [status(thm)], [c_231, c_193])).
% 2.69/1.42  tff(c_288, plain, (![A_116]: (~r2_hidden(A_116, '#skF_9'))), inference(splitLeft, [status(thm)], [c_260])).
% 2.69/1.42  tff(c_313, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_288])).
% 2.69/1.42  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.42  tff(c_98, plain, (![A_60, B_61]: (r2_hidden('#skF_2'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.42  tff(c_108, plain, (![A_60, B_61]: (~v1_xboole_0(A_60) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_98, c_2])).
% 2.69/1.42  tff(c_125, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.42  tff(c_135, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_108, c_125])).
% 2.69/1.42  tff(c_145, plain, (![B_70, A_71]: (B_70=A_71 | ~v1_xboole_0(B_70) | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_108, c_135])).
% 2.69/1.42  tff(c_148, plain, (![A_71]: (k1_xboole_0=A_71 | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_12, c_145])).
% 2.69/1.42  tff(c_316, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_313, c_148])).
% 2.69/1.42  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_316])).
% 2.69/1.42  tff(c_324, plain, (![B_117]: (r2_hidden(B_117, '#skF_9') | ~r2_hidden(B_117, '#skF_10'))), inference(splitRight, [status(thm)], [c_260])).
% 2.69/1.42  tff(c_987, plain, (![B_166]: (r2_hidden('#skF_2'('#skF_10', B_166), '#skF_9') | r1_tarski('#skF_10', B_166))), inference(resolution, [status(thm)], [c_10, c_324])).
% 2.69/1.42  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.42  tff(c_998, plain, (r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_987, c_8])).
% 2.69/1.42  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.42  tff(c_1060, plain, ('#skF_10'='#skF_9' | ~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_998, c_14])).
% 2.69/1.42  tff(c_1069, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_56, c_1060])).
% 2.69/1.42  tff(c_58, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.42  tff(c_344, plain, (r2_hidden('#skF_1'('#skF_10'), '#skF_9') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_324])).
% 2.69/1.42  tff(c_369, plain, (v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_344])).
% 2.69/1.42  tff(c_372, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_369, c_148])).
% 2.69/1.42  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_372])).
% 2.69/1.42  tff(c_380, plain, (~v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_344])).
% 2.69/1.42  tff(c_179, plain, (![A_80, C_81, B_82, D_83]: (r2_hidden(A_80, C_81) | ~r2_hidden(k4_tarski(A_80, B_82), k2_zfmisc_1(C_81, D_83)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.69/1.42  tff(c_182, plain, (![A_80, B_82]: (r2_hidden(A_80, '#skF_10') | ~r2_hidden(k4_tarski(A_80, B_82), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_179])).
% 2.69/1.42  tff(c_261, plain, (![A_109, B_110]: (r2_hidden(A_109, '#skF_10') | ~r2_hidden(B_110, '#skF_10') | ~r2_hidden(A_109, '#skF_9'))), inference(resolution, [status(thm)], [c_231, c_182])).
% 2.69/1.42  tff(c_508, plain, (![B_128]: (~r2_hidden(B_128, '#skF_10'))), inference(splitLeft, [status(thm)], [c_261])).
% 2.69/1.42  tff(c_528, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_508])).
% 2.69/1.42  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_380, c_528])).
% 2.69/1.42  tff(c_631, plain, (![A_136]: (r2_hidden(A_136, '#skF_10') | ~r2_hidden(A_136, '#skF_9'))), inference(splitRight, [status(thm)], [c_261])).
% 2.69/1.42  tff(c_1096, plain, (![A_174]: (r1_tarski(A_174, '#skF_10') | ~r2_hidden('#skF_2'(A_174, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_631, c_8])).
% 2.69/1.42  tff(c_1108, plain, (r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_10, c_1096])).
% 2.69/1.42  tff(c_1115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1069, c_1069, c_1108])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 0
% 2.69/1.42  #Sup     : 235
% 2.69/1.42  #Fact    : 0
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 4
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 65
% 2.69/1.42  #Demod        : 41
% 2.69/1.42  #Tautology    : 46
% 2.69/1.42  #SimpNegUnit  : 11
% 2.69/1.42  #BackRed      : 2
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.30
% 2.69/1.42  Parsing              : 0.15
% 2.69/1.42  CNF conversion       : 0.03
% 2.69/1.42  Main loop            : 0.35
% 2.69/1.42  Inferencing          : 0.13
% 2.69/1.42  Reduction            : 0.09
% 2.69/1.42  Demodulation         : 0.06
% 2.69/1.42  BG Simplification    : 0.02
% 2.69/1.42  Subsumption          : 0.08
% 2.69/1.42  Abstraction          : 0.02
% 2.69/1.42  MUC search           : 0.00
% 2.69/1.42  Cooper               : 0.00
% 2.69/1.42  Total                : 0.68
% 2.69/1.42  Index Insertion      : 0.00
% 2.69/1.42  Index Deletion       : 0.00
% 2.69/1.42  Index Matching       : 0.00
% 2.69/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
