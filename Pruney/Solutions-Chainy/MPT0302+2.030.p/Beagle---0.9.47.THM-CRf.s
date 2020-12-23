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
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 151 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 323 expanded)
%              Number of equality atoms :   16 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_34,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_165,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( r2_hidden(k4_tarski(A_68,B_69),k2_zfmisc_1(C_70,D_71))
      | ~ r2_hidden(B_69,D_71)
      | ~ r2_hidden(A_68,C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_87,plain,(
    ! [B_41,D_42,A_43,C_44] :
      ( r2_hidden(B_41,D_42)
      | ~ r2_hidden(k4_tarski(A_43,B_41),k2_zfmisc_1(C_44,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    ! [B_41,A_43] :
      ( r2_hidden(B_41,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_43,B_41),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_185,plain,(
    ! [B_69,A_68] :
      ( r2_hidden(B_69,'#skF_6')
      | ~ r2_hidden(B_69,'#skF_5')
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_165,c_90])).

tff(c_212,plain,(
    ! [A_74] : ~ r2_hidden(A_74,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_245,plain,(
    ! [B_75] : r1_tarski('#skF_6',B_75) ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_26,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),B_12)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden('#skF_4'(A_54,B_55),B_56)
      | ~ r1_tarski(B_55,B_56)
      | ~ r2_xboole_0(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_24,c_76])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_4'(A_11,B_12),A_11)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [B_57,B_58] :
      ( ~ r1_tarski(B_57,B_58)
      | ~ r2_xboole_0(B_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_103,c_22])).

tff(c_117,plain,(
    ! [B_59,A_60] :
      ( ~ r1_tarski(B_59,A_60)
      | B_59 = A_60
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_112])).

tff(c_126,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_249,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_245,c_126])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_249])).

tff(c_257,plain,(
    ! [B_76] :
      ( r2_hidden(B_76,'#skF_6')
      | ~ r2_hidden(B_76,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_290,plain,(
    ! [B_77] :
      ( r2_hidden('#skF_1'('#skF_5',B_77),'#skF_6')
      | r1_tarski('#skF_5',B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_298,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_290,c_4])).

tff(c_116,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_112])).

tff(c_300,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_298,c_116])).

tff(c_303,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_300])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_83,plain,(
    ! [A_37,C_38,B_39,D_40] :
      ( r2_hidden(A_37,C_38)
      | ~ r2_hidden(k4_tarski(A_37,B_39),k2_zfmisc_1(C_38,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_86,plain,(
    ! [A_37,B_39] :
      ( r2_hidden(A_37,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_37,B_39),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_83])).

tff(c_186,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(A_68,'#skF_5')
      | ~ r2_hidden(B_69,'#skF_5')
      | ~ r2_hidden(A_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_165,c_86])).

tff(c_340,plain,(
    ! [B_81] : ~ r2_hidden(B_81,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_375,plain,(
    ! [B_82] : r1_tarski('#skF_5',B_82) ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_379,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_375,c_126])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_379])).

tff(c_387,plain,(
    ! [A_83] :
      ( r2_hidden(A_83,'#skF_5')
      | ~ r2_hidden(A_83,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_414,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_84,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_387,c_4])).

tff(c_426,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_414])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_303,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.10/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.29  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.10/1.29  
% 2.40/1.31  tff(f_73, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.40/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.40/1.31  tff(f_64, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.40/1.31  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.40/1.31  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.40/1.31  tff(f_56, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.40/1.31  tff(c_34, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.31  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.31  tff(c_165, plain, (![A_68, B_69, C_70, D_71]: (r2_hidden(k4_tarski(A_68, B_69), k2_zfmisc_1(C_70, D_71)) | ~r2_hidden(B_69, D_71) | ~r2_hidden(A_68, C_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.31  tff(c_40, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.31  tff(c_87, plain, (![B_41, D_42, A_43, C_44]: (r2_hidden(B_41, D_42) | ~r2_hidden(k4_tarski(A_43, B_41), k2_zfmisc_1(C_44, D_42)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.31  tff(c_90, plain, (![B_41, A_43]: (r2_hidden(B_41, '#skF_6') | ~r2_hidden(k4_tarski(A_43, B_41), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_87])).
% 2.40/1.31  tff(c_185, plain, (![B_69, A_68]: (r2_hidden(B_69, '#skF_6') | ~r2_hidden(B_69, '#skF_5') | ~r2_hidden(A_68, '#skF_6'))), inference(resolution, [status(thm)], [c_165, c_90])).
% 2.40/1.31  tff(c_212, plain, (![A_74]: (~r2_hidden(A_74, '#skF_6'))), inference(splitLeft, [status(thm)], [c_185])).
% 2.40/1.31  tff(c_245, plain, (![B_75]: (r1_tarski('#skF_6', B_75))), inference(resolution, [status(thm)], [c_6, c_212])).
% 2.40/1.31  tff(c_26, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.40/1.31  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.40/1.31  tff(c_24, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), B_12) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.31  tff(c_76, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.31  tff(c_103, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_4'(A_54, B_55), B_56) | ~r1_tarski(B_55, B_56) | ~r2_xboole_0(A_54, B_55))), inference(resolution, [status(thm)], [c_24, c_76])).
% 2.40/1.31  tff(c_22, plain, (![A_11, B_12]: (~r2_hidden('#skF_4'(A_11, B_12), A_11) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.40/1.31  tff(c_112, plain, (![B_57, B_58]: (~r1_tarski(B_57, B_58) | ~r2_xboole_0(B_58, B_57))), inference(resolution, [status(thm)], [c_103, c_22])).
% 2.40/1.31  tff(c_117, plain, (![B_59, A_60]: (~r1_tarski(B_59, A_60) | B_59=A_60 | ~r1_tarski(A_60, B_59))), inference(resolution, [status(thm)], [c_8, c_112])).
% 2.40/1.31  tff(c_126, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_117])).
% 2.40/1.31  tff(c_249, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_245, c_126])).
% 2.40/1.31  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_249])).
% 2.40/1.31  tff(c_257, plain, (![B_76]: (r2_hidden(B_76, '#skF_6') | ~r2_hidden(B_76, '#skF_5'))), inference(splitRight, [status(thm)], [c_185])).
% 2.40/1.31  tff(c_290, plain, (![B_77]: (r2_hidden('#skF_1'('#skF_5', B_77), '#skF_6') | r1_tarski('#skF_5', B_77))), inference(resolution, [status(thm)], [c_6, c_257])).
% 2.40/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.40/1.31  tff(c_298, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_290, c_4])).
% 2.40/1.31  tff(c_116, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_112])).
% 2.40/1.31  tff(c_300, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_298, c_116])).
% 2.40/1.31  tff(c_303, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_300])).
% 2.40/1.31  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.31  tff(c_83, plain, (![A_37, C_38, B_39, D_40]: (r2_hidden(A_37, C_38) | ~r2_hidden(k4_tarski(A_37, B_39), k2_zfmisc_1(C_38, D_40)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.40/1.31  tff(c_86, plain, (![A_37, B_39]: (r2_hidden(A_37, '#skF_5') | ~r2_hidden(k4_tarski(A_37, B_39), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_83])).
% 2.40/1.31  tff(c_186, plain, (![A_68, B_69]: (r2_hidden(A_68, '#skF_5') | ~r2_hidden(B_69, '#skF_5') | ~r2_hidden(A_68, '#skF_6'))), inference(resolution, [status(thm)], [c_165, c_86])).
% 2.40/1.31  tff(c_340, plain, (![B_81]: (~r2_hidden(B_81, '#skF_5'))), inference(splitLeft, [status(thm)], [c_186])).
% 2.40/1.31  tff(c_375, plain, (![B_82]: (r1_tarski('#skF_5', B_82))), inference(resolution, [status(thm)], [c_6, c_340])).
% 2.40/1.31  tff(c_379, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_375, c_126])).
% 2.40/1.31  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_379])).
% 2.40/1.31  tff(c_387, plain, (![A_83]: (r2_hidden(A_83, '#skF_5') | ~r2_hidden(A_83, '#skF_6'))), inference(splitRight, [status(thm)], [c_186])).
% 2.40/1.31  tff(c_414, plain, (![A_84]: (r1_tarski(A_84, '#skF_5') | ~r2_hidden('#skF_1'(A_84, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_387, c_4])).
% 2.40/1.31  tff(c_426, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_414])).
% 2.40/1.31  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_303, c_426])).
% 2.40/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  Inference rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Ref     : 0
% 2.40/1.31  #Sup     : 77
% 2.40/1.31  #Fact    : 0
% 2.40/1.31  #Define  : 0
% 2.40/1.31  #Split   : 2
% 2.40/1.31  #Chain   : 0
% 2.40/1.31  #Close   : 0
% 2.40/1.31  
% 2.40/1.31  Ordering : KBO
% 2.40/1.31  
% 2.40/1.31  Simplification rules
% 2.40/1.31  ----------------------
% 2.40/1.31  #Subsume      : 8
% 2.40/1.31  #Demod        : 5
% 2.40/1.31  #Tautology    : 20
% 2.40/1.31  #SimpNegUnit  : 7
% 2.40/1.31  #BackRed      : 2
% 2.40/1.31  
% 2.40/1.31  #Partial instantiations: 0
% 2.40/1.31  #Strategies tried      : 1
% 2.40/1.31  
% 2.40/1.31  Timing (in seconds)
% 2.40/1.31  ----------------------
% 2.40/1.31  Preprocessing        : 0.29
% 2.40/1.31  Parsing              : 0.15
% 2.40/1.31  CNF conversion       : 0.02
% 2.40/1.31  Main loop            : 0.25
% 2.40/1.31  Inferencing          : 0.10
% 2.40/1.31  Reduction            : 0.06
% 2.40/1.31  Demodulation         : 0.04
% 2.40/1.31  BG Simplification    : 0.02
% 2.40/1.31  Subsumption          : 0.06
% 2.40/1.31  Abstraction          : 0.01
% 2.40/1.31  MUC search           : 0.00
% 2.40/1.31  Cooper               : 0.00
% 2.40/1.31  Total                : 0.57
% 2.40/1.31  Index Insertion      : 0.00
% 2.40/1.31  Index Deletion       : 0.00
% 2.40/1.31  Index Matching       : 0.00
% 2.40/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
