%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:48 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 128 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 251 expanded)
%              Number of equality atoms :   18 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_48,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_221,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( r2_hidden(k4_tarski(A_69,B_70),k2_zfmisc_1(C_71,D_72))
      | ~ r2_hidden(B_70,D_72)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_146,plain,(
    ! [A_50,C_51,B_52,D_53] :
      ( r2_hidden(A_50,C_51)
      | ~ r2_hidden(k4_tarski(A_50,B_52),k2_zfmisc_1(C_51,D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_149,plain,(
    ! [A_50,B_52] :
      ( r2_hidden(A_50,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_50,B_52),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_146])).

tff(c_244,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(A_69,'#skF_5')
      | ~ r2_hidden(B_70,'#skF_5')
      | ~ r2_hidden(A_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_221,c_149])).

tff(c_251,plain,(
    ! [B_73] : ~ r2_hidden(B_73,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_257,plain,(
    ! [B_74] : r1_tarski('#skF_5',B_74) ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_87,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_1'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    ! [C_26,B_27] : ~ r2_hidden(C_26,k4_xboole_0(B_27,k1_tarski(C_26))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    ! [C_26] : ~ r2_hidden(C_26,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_73])).

tff(c_97,plain,(
    ! [B_33] : r1_tarski(k1_xboole_0,B_33) ),
    inference(resolution,[status(thm)],[c_87,c_76])).

tff(c_115,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    ! [B_33] :
      ( k1_xboole_0 = B_33
      | ~ r1_tarski(B_33,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_97,c_115])).

tff(c_261,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_257,c_120])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_261])).

tff(c_292,plain,(
    ! [A_77] :
      ( r2_hidden(A_77,'#skF_5')
      | ~ r2_hidden(A_77,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_304,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_78,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_309,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_304])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_311,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_309,c_26])).

tff(c_314,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_311])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_269,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(k4_tarski(A_75,B_76),k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(B_76,'#skF_4')
      | ~ r2_hidden(A_75,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_221])).

tff(c_40,plain,(
    ! [A_16,C_18,B_17,D_19] :
      ( r2_hidden(A_16,C_18)
      | ~ r2_hidden(k4_tarski(A_16,B_17),k2_zfmisc_1(C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_289,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,'#skF_4')
      | ~ r2_hidden(B_76,'#skF_4')
      | ~ r2_hidden(A_75,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_269,c_40])).

tff(c_330,plain,(
    ! [B_82] : ~ r2_hidden(B_82,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_337,plain,(
    ! [B_83] : r1_tarski('#skF_4',B_83) ),
    inference(resolution,[status(thm)],[c_6,c_330])).

tff(c_341,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_337,c_120])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_341])).

tff(c_370,plain,(
    ! [A_86] :
      ( r2_hidden(A_86,'#skF_4')
      | ~ r2_hidden(A_86,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_380,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_1'('#skF_5',B_87),'#skF_4')
      | r1_tarski('#skF_5',B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_370])).

tff(c_392,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_380,c_4])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_314,c_392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.31  
% 2.03/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.31  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.03/1.31  
% 2.03/1.31  %Foreground sorts:
% 2.03/1.31  
% 2.03/1.31  
% 2.03/1.31  %Background operators:
% 2.03/1.31  
% 2.03/1.31  
% 2.03/1.31  %Foreground operators:
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.31  
% 2.28/1.32  tff(f_74, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.28/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.28/1.32  tff(f_58, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.28/1.32  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.28/1.32  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.28/1.32  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.28/1.32  tff(c_48, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.32  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.32  tff(c_221, plain, (![A_69, B_70, C_71, D_72]: (r2_hidden(k4_tarski(A_69, B_70), k2_zfmisc_1(C_71, D_72)) | ~r2_hidden(B_70, D_72) | ~r2_hidden(A_69, C_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.32  tff(c_54, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.32  tff(c_146, plain, (![A_50, C_51, B_52, D_53]: (r2_hidden(A_50, C_51) | ~r2_hidden(k4_tarski(A_50, B_52), k2_zfmisc_1(C_51, D_53)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.32  tff(c_149, plain, (![A_50, B_52]: (r2_hidden(A_50, '#skF_5') | ~r2_hidden(k4_tarski(A_50, B_52), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_54, c_146])).
% 2.28/1.32  tff(c_244, plain, (![A_69, B_70]: (r2_hidden(A_69, '#skF_5') | ~r2_hidden(B_70, '#skF_5') | ~r2_hidden(A_69, '#skF_4'))), inference(resolution, [status(thm)], [c_221, c_149])).
% 2.28/1.32  tff(c_251, plain, (![B_73]: (~r2_hidden(B_73, '#skF_5'))), inference(splitLeft, [status(thm)], [c_244])).
% 2.28/1.32  tff(c_257, plain, (![B_74]: (r1_tarski('#skF_5', B_74))), inference(resolution, [status(thm)], [c_6, c_251])).
% 2.28/1.32  tff(c_87, plain, (![A_32, B_33]: (r2_hidden('#skF_1'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.32  tff(c_32, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.32  tff(c_73, plain, (![C_26, B_27]: (~r2_hidden(C_26, k4_xboole_0(B_27, k1_tarski(C_26))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.32  tff(c_76, plain, (![C_26]: (~r2_hidden(C_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_73])).
% 2.28/1.32  tff(c_97, plain, (![B_33]: (r1_tarski(k1_xboole_0, B_33))), inference(resolution, [status(thm)], [c_87, c_76])).
% 2.28/1.32  tff(c_115, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.32  tff(c_120, plain, (![B_33]: (k1_xboole_0=B_33 | ~r1_tarski(B_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_97, c_115])).
% 2.28/1.32  tff(c_261, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_257, c_120])).
% 2.28/1.32  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_261])).
% 2.28/1.32  tff(c_292, plain, (![A_77]: (r2_hidden(A_77, '#skF_5') | ~r2_hidden(A_77, '#skF_4'))), inference(splitRight, [status(thm)], [c_244])).
% 2.28/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.32  tff(c_304, plain, (![A_78]: (r1_tarski(A_78, '#skF_5') | ~r2_hidden('#skF_1'(A_78, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_292, c_4])).
% 2.28/1.32  tff(c_309, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_304])).
% 2.28/1.32  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.32  tff(c_311, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_309, c_26])).
% 2.28/1.32  tff(c_314, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_311])).
% 2.28/1.32  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.32  tff(c_269, plain, (![A_75, B_76]: (r2_hidden(k4_tarski(A_75, B_76), k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(B_76, '#skF_4') | ~r2_hidden(A_75, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_221])).
% 2.28/1.32  tff(c_40, plain, (![A_16, C_18, B_17, D_19]: (r2_hidden(A_16, C_18) | ~r2_hidden(k4_tarski(A_16, B_17), k2_zfmisc_1(C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.28/1.32  tff(c_289, plain, (![A_75, B_76]: (r2_hidden(A_75, '#skF_4') | ~r2_hidden(B_76, '#skF_4') | ~r2_hidden(A_75, '#skF_5'))), inference(resolution, [status(thm)], [c_269, c_40])).
% 2.28/1.32  tff(c_330, plain, (![B_82]: (~r2_hidden(B_82, '#skF_4'))), inference(splitLeft, [status(thm)], [c_289])).
% 2.28/1.32  tff(c_337, plain, (![B_83]: (r1_tarski('#skF_4', B_83))), inference(resolution, [status(thm)], [c_6, c_330])).
% 2.28/1.32  tff(c_341, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_337, c_120])).
% 2.28/1.32  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_341])).
% 2.28/1.32  tff(c_370, plain, (![A_86]: (r2_hidden(A_86, '#skF_4') | ~r2_hidden(A_86, '#skF_5'))), inference(splitRight, [status(thm)], [c_289])).
% 2.28/1.32  tff(c_380, plain, (![B_87]: (r2_hidden('#skF_1'('#skF_5', B_87), '#skF_4') | r1_tarski('#skF_5', B_87))), inference(resolution, [status(thm)], [c_6, c_370])).
% 2.28/1.32  tff(c_392, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_380, c_4])).
% 2.28/1.32  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_314, c_392])).
% 2.28/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  Inference rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Ref     : 0
% 2.28/1.32  #Sup     : 72
% 2.28/1.32  #Fact    : 0
% 2.28/1.32  #Define  : 0
% 2.28/1.32  #Split   : 3
% 2.28/1.32  #Chain   : 0
% 2.28/1.32  #Close   : 0
% 2.28/1.32  
% 2.28/1.32  Ordering : KBO
% 2.28/1.32  
% 2.28/1.32  Simplification rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Subsume      : 16
% 2.28/1.32  #Demod        : 6
% 2.28/1.32  #Tautology    : 23
% 2.28/1.32  #SimpNegUnit  : 11
% 2.28/1.32  #BackRed      : 3
% 2.28/1.32  
% 2.28/1.32  #Partial instantiations: 0
% 2.28/1.32  #Strategies tried      : 1
% 2.28/1.32  
% 2.28/1.32  Timing (in seconds)
% 2.28/1.32  ----------------------
% 2.28/1.33  Preprocessing        : 0.31
% 2.28/1.33  Parsing              : 0.16
% 2.28/1.33  CNF conversion       : 0.02
% 2.28/1.33  Main loop            : 0.22
% 2.28/1.33  Inferencing          : 0.08
% 2.28/1.33  Reduction            : 0.06
% 2.28/1.33  Demodulation         : 0.04
% 2.28/1.33  BG Simplification    : 0.01
% 2.28/1.33  Subsumption          : 0.05
% 2.28/1.33  Abstraction          : 0.01
% 2.28/1.33  MUC search           : 0.00
% 2.28/1.33  Cooper               : 0.00
% 2.28/1.33  Total                : 0.56
% 2.28/1.33  Index Insertion      : 0.00
% 2.28/1.33  Index Deletion       : 0.00
% 2.28/1.33  Index Matching       : 0.00
% 2.28/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
