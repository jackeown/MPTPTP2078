%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:48 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 116 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 227 expanded)
%              Number of equality atoms :   19 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_208,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),B_66)
      | r2_hidden('#skF_3'(A_65,B_66),A_65)
      | B_66 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [C_23,B_24] : ~ r2_hidden(C_23,k4_xboole_0(B_24,k1_tarski(C_23))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ! [C_23] : ~ r2_hidden(C_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_232,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_66),B_66)
      | k1_xboole_0 = B_66 ) ),
    inference(resolution,[status(thm)],[c_208,c_66])).

tff(c_317,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_hidden(k4_tarski(A_76,B_77),k2_zfmisc_1(C_78,D_79))
      | ~ r2_hidden(B_77,D_79)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_128,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r2_hidden(A_44,C_45)
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1(C_45,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,(
    ! [A_44,B_46] :
      ( r2_hidden(A_44,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_128])).

tff(c_337,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,'#skF_5')
      | ~ r2_hidden(B_77,'#skF_5')
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_317,c_131])).

tff(c_344,plain,(
    ! [B_80] : ~ r2_hidden(B_80,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_356,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_232,c_344])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_356])).

tff(c_378,plain,(
    ! [A_81] :
      ( r2_hidden(A_81,'#skF_5')
      | ~ r2_hidden(A_81,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_416,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_84,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_378,c_4])).

tff(c_426,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_416])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_428,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_426,c_16])).

tff(c_431,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_428])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_396,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(k4_tarski(A_82,B_83),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_83,'#skF_4')
      | ~ r2_hidden(A_82,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_317])).

tff(c_30,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_413,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(A_82,'#skF_4')
      | ~ r2_hidden(B_83,'#skF_4')
      | ~ r2_hidden(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_396,c_30])).

tff(c_434,plain,(
    ! [B_85] : ~ r2_hidden(B_85,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_446,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_232,c_434])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_446])).

tff(c_468,plain,(
    ! [A_86] :
      ( r2_hidden(A_86,'#skF_4')
      | ~ r2_hidden(A_86,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_514,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_1'('#skF_5',B_88),'#skF_4')
      | r1_tarski('#skF_5',B_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_468])).

tff(c_524,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_514,c_4])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_431,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.61/1.41  
% 2.61/1.41  %Foreground sorts:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Background operators:
% 2.61/1.41  
% 2.61/1.41  
% 2.61/1.41  %Foreground operators:
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.61/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.41  
% 2.61/1.42  tff(f_71, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.61/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.61/1.42  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.61/1.42  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.61/1.42  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.61/1.42  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.61/1.42  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.42  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.42  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.42  tff(c_208, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), B_66) | r2_hidden('#skF_3'(A_65, B_66), A_65) | B_66=A_65)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.42  tff(c_22, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.42  tff(c_63, plain, (![C_23, B_24]: (~r2_hidden(C_23, k4_xboole_0(B_24, k1_tarski(C_23))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.61/1.42  tff(c_66, plain, (![C_23]: (~r2_hidden(C_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_63])).
% 2.61/1.42  tff(c_232, plain, (![B_66]: (r2_hidden('#skF_2'(k1_xboole_0, B_66), B_66) | k1_xboole_0=B_66)), inference(resolution, [status(thm)], [c_208, c_66])).
% 2.61/1.42  tff(c_317, plain, (![A_76, B_77, C_78, D_79]: (r2_hidden(k4_tarski(A_76, B_77), k2_zfmisc_1(C_78, D_79)) | ~r2_hidden(B_77, D_79) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.42  tff(c_44, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.42  tff(c_128, plain, (![A_44, C_45, B_46, D_47]: (r2_hidden(A_44, C_45) | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1(C_45, D_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.42  tff(c_131, plain, (![A_44, B_46]: (r2_hidden(A_44, '#skF_5') | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_128])).
% 2.61/1.42  tff(c_337, plain, (![A_76, B_77]: (r2_hidden(A_76, '#skF_5') | ~r2_hidden(B_77, '#skF_5') | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_317, c_131])).
% 2.61/1.42  tff(c_344, plain, (![B_80]: (~r2_hidden(B_80, '#skF_5'))), inference(splitLeft, [status(thm)], [c_337])).
% 2.61/1.42  tff(c_356, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_232, c_344])).
% 2.61/1.42  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_356])).
% 2.61/1.42  tff(c_378, plain, (![A_81]: (r2_hidden(A_81, '#skF_5') | ~r2_hidden(A_81, '#skF_4'))), inference(splitRight, [status(thm)], [c_337])).
% 2.61/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.42  tff(c_416, plain, (![A_84]: (r1_tarski(A_84, '#skF_5') | ~r2_hidden('#skF_1'(A_84, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_378, c_4])).
% 2.61/1.42  tff(c_426, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_416])).
% 2.61/1.42  tff(c_16, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.42  tff(c_428, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_426, c_16])).
% 2.61/1.42  tff(c_431, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_428])).
% 2.61/1.42  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.42  tff(c_396, plain, (![A_82, B_83]: (r2_hidden(k4_tarski(A_82, B_83), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_83, '#skF_4') | ~r2_hidden(A_82, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_317])).
% 2.61/1.42  tff(c_30, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.42  tff(c_413, plain, (![A_82, B_83]: (r2_hidden(A_82, '#skF_4') | ~r2_hidden(B_83, '#skF_4') | ~r2_hidden(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_396, c_30])).
% 2.61/1.42  tff(c_434, plain, (![B_85]: (~r2_hidden(B_85, '#skF_4'))), inference(splitLeft, [status(thm)], [c_413])).
% 2.61/1.42  tff(c_446, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_232, c_434])).
% 2.61/1.42  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_446])).
% 2.61/1.42  tff(c_468, plain, (![A_86]: (r2_hidden(A_86, '#skF_4') | ~r2_hidden(A_86, '#skF_5'))), inference(splitRight, [status(thm)], [c_413])).
% 2.61/1.42  tff(c_514, plain, (![B_88]: (r2_hidden('#skF_1'('#skF_5', B_88), '#skF_4') | r1_tarski('#skF_5', B_88))), inference(resolution, [status(thm)], [c_6, c_468])).
% 2.61/1.42  tff(c_524, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_514, c_4])).
% 2.61/1.42  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_431, c_431, c_524])).
% 2.61/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.42  
% 2.61/1.42  Inference rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Ref     : 0
% 2.61/1.42  #Sup     : 97
% 2.61/1.42  #Fact    : 0
% 2.61/1.42  #Define  : 0
% 2.61/1.42  #Split   : 2
% 2.61/1.42  #Chain   : 0
% 2.61/1.42  #Close   : 0
% 2.61/1.42  
% 2.61/1.42  Ordering : KBO
% 2.61/1.42  
% 2.61/1.42  Simplification rules
% 2.61/1.42  ----------------------
% 2.61/1.42  #Subsume      : 14
% 2.61/1.42  #Demod        : 7
% 2.61/1.42  #Tautology    : 27
% 2.61/1.42  #SimpNegUnit  : 9
% 2.61/1.42  #BackRed      : 2
% 2.61/1.42  
% 2.61/1.42  #Partial instantiations: 0
% 2.61/1.42  #Strategies tried      : 1
% 2.61/1.42  
% 2.61/1.42  Timing (in seconds)
% 2.61/1.42  ----------------------
% 2.61/1.43  Preprocessing        : 0.33
% 2.61/1.43  Parsing              : 0.17
% 2.61/1.43  CNF conversion       : 0.03
% 2.61/1.43  Main loop            : 0.28
% 2.61/1.43  Inferencing          : 0.11
% 2.61/1.43  Reduction            : 0.07
% 2.61/1.43  Demodulation         : 0.05
% 2.61/1.43  BG Simplification    : 0.01
% 2.61/1.43  Subsumption          : 0.06
% 2.61/1.43  Abstraction          : 0.01
% 2.61/1.43  MUC search           : 0.00
% 2.61/1.43  Cooper               : 0.00
% 2.61/1.43  Total                : 0.63
% 2.61/1.43  Index Insertion      : 0.00
% 2.61/1.43  Index Deletion       : 0.00
% 2.61/1.43  Index Matching       : 0.00
% 2.61/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
