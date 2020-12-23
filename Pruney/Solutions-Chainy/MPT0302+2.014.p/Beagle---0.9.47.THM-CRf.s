%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:48 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 122 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 237 expanded)
%              Number of equality atoms :   18 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_36,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_227,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_2'(A_74,B_75),B_75)
      | r2_hidden('#skF_3'(A_74,B_75),A_74)
      | B_75 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    ! [A_16,C_29] :
      ( ~ r1_xboole_0(A_16,k1_xboole_0)
      | ~ r2_hidden(C_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_58])).

tff(c_63,plain,(
    ! [C_29] : ~ r2_hidden(C_29,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_61])).

tff(c_256,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_75),B_75)
      | k1_xboole_0 = B_75 ) ),
    inference(resolution,[status(thm)],[c_227,c_63])).

tff(c_258,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_hidden(k4_tarski(A_76,B_77),k2_zfmisc_1(C_78,D_79))
      | ~ r2_hidden(B_77,D_79)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_148,plain,(
    ! [A_53,C_54,B_55,D_56] :
      ( r2_hidden(A_53,C_54)
      | ~ r2_hidden(k4_tarski(A_53,B_55),k2_zfmisc_1(C_54,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_151,plain,(
    ! [A_53,B_55] :
      ( r2_hidden(A_53,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_53,B_55),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_148])).

tff(c_278,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,'#skF_5')
      | ~ r2_hidden(B_77,'#skF_5')
      | ~ r2_hidden(A_76,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_258,c_151])).

tff(c_304,plain,(
    ! [B_81] : ~ r2_hidden(B_81,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_308,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_256,c_304])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_308])).

tff(c_332,plain,(
    ! [A_82] :
      ( r2_hidden(A_82,'#skF_5')
      | ~ r2_hidden(A_82,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_350,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_83,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_332,c_4])).

tff(c_360,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_350])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_376,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_360,c_20])).

tff(c_379,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_376])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_130,plain,(
    ! [B_45,D_46,A_47,C_48] :
      ( r2_hidden(B_45,D_46)
      | ~ r2_hidden(k4_tarski(A_47,B_45),k2_zfmisc_1(C_48,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_133,plain,(
    ! [B_45,A_47] :
      ( r2_hidden(B_45,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_47,B_45),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_130])).

tff(c_280,plain,(
    ! [B_77,A_76] :
      ( r2_hidden(B_77,'#skF_6')
      | ~ r2_hidden(B_77,'#skF_5')
      | ~ r2_hidden(A_76,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_258,c_133])).

tff(c_426,plain,(
    ! [A_93] : ~ r2_hidden(A_93,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_434,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_256,c_426])).

tff(c_457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_434])).

tff(c_459,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,'#skF_6')
      | ~ r2_hidden(B_94,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_591,plain,(
    ! [B_100] :
      ( r2_hidden('#skF_1'('#skF_5',B_100),'#skF_6')
      | r1_tarski('#skF_5',B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_459])).

tff(c_601,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_591,c_4])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_379,c_601])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.45/1.33  
% 2.45/1.33  %Foreground sorts:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Background operators:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Foreground operators:
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.45/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.45/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.45/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.45/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.45/1.33  
% 2.45/1.35  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.45/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.35  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.45/1.35  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.45/1.35  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.45/1.35  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.45/1.35  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.45/1.35  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.45/1.35  tff(c_36, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.35  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_227, plain, (![A_74, B_75]: (r2_hidden('#skF_2'(A_74, B_75), B_75) | r2_hidden('#skF_3'(A_74, B_75), A_74) | B_75=A_74)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.35  tff(c_28, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.35  tff(c_26, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.35  tff(c_58, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.45/1.35  tff(c_61, plain, (![A_16, C_29]: (~r1_xboole_0(A_16, k1_xboole_0) | ~r2_hidden(C_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_58])).
% 2.45/1.35  tff(c_63, plain, (![C_29]: (~r2_hidden(C_29, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_61])).
% 2.45/1.35  tff(c_256, plain, (![B_75]: (r2_hidden('#skF_2'(k1_xboole_0, B_75), B_75) | k1_xboole_0=B_75)), inference(resolution, [status(thm)], [c_227, c_63])).
% 2.45/1.35  tff(c_258, plain, (![A_76, B_77, C_78, D_79]: (r2_hidden(k4_tarski(A_76, B_77), k2_zfmisc_1(C_78, D_79)) | ~r2_hidden(B_77, D_79) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.35  tff(c_42, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_148, plain, (![A_53, C_54, B_55, D_56]: (r2_hidden(A_53, C_54) | ~r2_hidden(k4_tarski(A_53, B_55), k2_zfmisc_1(C_54, D_56)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.35  tff(c_151, plain, (![A_53, B_55]: (r2_hidden(A_53, '#skF_5') | ~r2_hidden(k4_tarski(A_53, B_55), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_148])).
% 2.45/1.35  tff(c_278, plain, (![A_76, B_77]: (r2_hidden(A_76, '#skF_5') | ~r2_hidden(B_77, '#skF_5') | ~r2_hidden(A_76, '#skF_6'))), inference(resolution, [status(thm)], [c_258, c_151])).
% 2.45/1.35  tff(c_304, plain, (![B_81]: (~r2_hidden(B_81, '#skF_5'))), inference(splitLeft, [status(thm)], [c_278])).
% 2.45/1.35  tff(c_308, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_256, c_304])).
% 2.45/1.35  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_308])).
% 2.45/1.35  tff(c_332, plain, (![A_82]: (r2_hidden(A_82, '#skF_5') | ~r2_hidden(A_82, '#skF_6'))), inference(splitRight, [status(thm)], [c_278])).
% 2.45/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.35  tff(c_350, plain, (![A_83]: (r1_tarski(A_83, '#skF_5') | ~r2_hidden('#skF_1'(A_83, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_332, c_4])).
% 2.45/1.35  tff(c_360, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_350])).
% 2.45/1.35  tff(c_20, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.35  tff(c_376, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_360, c_20])).
% 2.45/1.35  tff(c_379, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_36, c_376])).
% 2.45/1.35  tff(c_38, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.35  tff(c_130, plain, (![B_45, D_46, A_47, C_48]: (r2_hidden(B_45, D_46) | ~r2_hidden(k4_tarski(A_47, B_45), k2_zfmisc_1(C_48, D_46)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.35  tff(c_133, plain, (![B_45, A_47]: (r2_hidden(B_45, '#skF_6') | ~r2_hidden(k4_tarski(A_47, B_45), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_130])).
% 2.45/1.35  tff(c_280, plain, (![B_77, A_76]: (r2_hidden(B_77, '#skF_6') | ~r2_hidden(B_77, '#skF_5') | ~r2_hidden(A_76, '#skF_6'))), inference(resolution, [status(thm)], [c_258, c_133])).
% 2.45/1.35  tff(c_426, plain, (![A_93]: (~r2_hidden(A_93, '#skF_6'))), inference(splitLeft, [status(thm)], [c_280])).
% 2.45/1.35  tff(c_434, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_256, c_426])).
% 2.45/1.35  tff(c_457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_434])).
% 2.45/1.35  tff(c_459, plain, (![B_94]: (r2_hidden(B_94, '#skF_6') | ~r2_hidden(B_94, '#skF_5'))), inference(splitRight, [status(thm)], [c_280])).
% 2.45/1.35  tff(c_591, plain, (![B_100]: (r2_hidden('#skF_1'('#skF_5', B_100), '#skF_6') | r1_tarski('#skF_5', B_100))), inference(resolution, [status(thm)], [c_6, c_459])).
% 2.45/1.35  tff(c_601, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_591, c_4])).
% 2.45/1.35  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_379, c_601])).
% 2.45/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  Inference rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Ref     : 0
% 2.45/1.35  #Sup     : 112
% 2.45/1.35  #Fact    : 0
% 2.45/1.35  #Define  : 0
% 2.45/1.35  #Split   : 2
% 2.45/1.35  #Chain   : 0
% 2.45/1.35  #Close   : 0
% 2.45/1.35  
% 2.45/1.35  Ordering : KBO
% 2.45/1.35  
% 2.45/1.35  Simplification rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Subsume      : 16
% 2.45/1.35  #Demod        : 19
% 2.45/1.35  #Tautology    : 32
% 2.45/1.35  #SimpNegUnit  : 11
% 2.45/1.35  #BackRed      : 2
% 2.45/1.35  
% 2.45/1.35  #Partial instantiations: 0
% 2.45/1.35  #Strategies tried      : 1
% 2.45/1.35  
% 2.45/1.35  Timing (in seconds)
% 2.45/1.35  ----------------------
% 2.45/1.35  Preprocessing        : 0.29
% 2.45/1.35  Parsing              : 0.15
% 2.45/1.35  CNF conversion       : 0.02
% 2.45/1.35  Main loop            : 0.29
% 2.45/1.35  Inferencing          : 0.12
% 2.45/1.35  Reduction            : 0.07
% 2.45/1.35  Demodulation         : 0.05
% 2.45/1.35  BG Simplification    : 0.01
% 2.45/1.35  Subsumption          : 0.06
% 2.45/1.35  Abstraction          : 0.01
% 2.45/1.35  MUC search           : 0.00
% 2.45/1.35  Cooper               : 0.00
% 2.45/1.35  Total                : 0.61
% 2.45/1.35  Index Insertion      : 0.00
% 2.45/1.35  Index Deletion       : 0.00
% 2.45/1.35  Index Matching       : 0.00
% 2.45/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
