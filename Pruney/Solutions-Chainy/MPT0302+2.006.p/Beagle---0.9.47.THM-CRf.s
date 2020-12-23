%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   52 (  86 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 158 expanded)
%              Number of equality atoms :   20 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,D_15))
      | ~ r2_hidden(B_13,D_15)
      | ~ r2_hidden(A_12,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_zfmisc_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_98,plain,(
    ! [A_32,C_33,B_34,D_35] :
      ( r2_hidden(A_32,C_33)
      | ~ r2_hidden(k4_tarski(A_32,B_34),k2_zfmisc_1(C_33,D_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,'#skF_3')
      | ~ r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_98])).

tff(c_126,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,'#skF_3')
      | ~ r2_hidden(B_13,'#skF_3')
      | ~ r2_hidden(A_12,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_121])).

tff(c_129,plain,(
    ! [B_46] : ~ r2_hidden(B_46,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_141,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_141])).

tff(c_155,plain,(
    ! [A_49] :
      ( r2_hidden(A_49,'#skF_3')
      | ~ r2_hidden(A_49,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_164,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_50,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_155,c_6])).

tff(c_169,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_173,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_169,c_12])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_102,plain,(
    ! [B_36,D_37,A_38,C_39] :
      ( r2_hidden(B_36,D_37)
      | ~ r2_hidden(k4_tarski(A_38,B_36),k2_zfmisc_1(C_39,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_149,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_48,B_47),k2_zfmisc_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_102])).

tff(c_154,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,'#skF_4')
      | ~ r2_hidden(B_13,'#skF_3')
      | ~ r2_hidden(A_12,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_194,plain,(
    ! [A_54] : ~ r2_hidden(A_54,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_210,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_194])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_210])).

tff(c_219,plain,(
    ! [B_55] :
      ( r2_hidden(B_55,'#skF_4')
      | ~ r2_hidden(B_55,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_275,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_3',B_59),'#skF_4')
      | r1_tarski('#skF_3',B_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_219])).

tff(c_289,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_275,c_6])).

tff(c_293,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_289,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_297,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_2])).

tff(c_309,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_297])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:03:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.05/1.25  
% 2.05/1.25  %Foreground sorts:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Background operators:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Foreground operators:
% 2.05/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.05/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.05/1.25  
% 2.05/1.27  tff(f_61, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.05/1.27  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/1.27  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.05/1.27  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.05/1.27  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.05/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.05/1.27  tff(c_20, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.27  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.05/1.27  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.27  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.05/1.27  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, D_15)) | ~r2_hidden(B_13, D_15) | ~r2_hidden(A_12, C_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.27  tff(c_26, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.27  tff(c_98, plain, (![A_32, C_33, B_34, D_35]: (r2_hidden(A_32, C_33) | ~r2_hidden(k4_tarski(A_32, B_34), k2_zfmisc_1(C_33, D_35)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.27  tff(c_121, plain, (![A_44, B_45]: (r2_hidden(A_44, '#skF_3') | ~r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_98])).
% 2.05/1.27  tff(c_126, plain, (![A_12, B_13]: (r2_hidden(A_12, '#skF_3') | ~r2_hidden(B_13, '#skF_3') | ~r2_hidden(A_12, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_121])).
% 2.05/1.27  tff(c_129, plain, (![B_46]: (~r2_hidden(B_46, '#skF_3'))), inference(splitLeft, [status(thm)], [c_126])).
% 2.05/1.27  tff(c_141, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10, c_129])).
% 2.05/1.27  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_141])).
% 2.05/1.27  tff(c_155, plain, (![A_49]: (r2_hidden(A_49, '#skF_3') | ~r2_hidden(A_49, '#skF_4'))), inference(splitRight, [status(thm)], [c_126])).
% 2.05/1.27  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.05/1.27  tff(c_164, plain, (![A_50]: (r1_tarski(A_50, '#skF_3') | ~r2_hidden('#skF_1'(A_50, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_155, c_6])).
% 2.05/1.27  tff(c_169, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_164])).
% 2.05/1.27  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.27  tff(c_173, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_169, c_12])).
% 2.05/1.27  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.27  tff(c_102, plain, (![B_36, D_37, A_38, C_39]: (r2_hidden(B_36, D_37) | ~r2_hidden(k4_tarski(A_38, B_36), k2_zfmisc_1(C_39, D_37)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.27  tff(c_149, plain, (![B_47, A_48]: (r2_hidden(B_47, '#skF_4') | ~r2_hidden(k4_tarski(A_48, B_47), k2_zfmisc_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_102])).
% 2.05/1.27  tff(c_154, plain, (![B_13, A_12]: (r2_hidden(B_13, '#skF_4') | ~r2_hidden(B_13, '#skF_3') | ~r2_hidden(A_12, '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_149])).
% 2.05/1.27  tff(c_194, plain, (![A_54]: (~r2_hidden(A_54, '#skF_4'))), inference(splitLeft, [status(thm)], [c_154])).
% 2.05/1.27  tff(c_210, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_194])).
% 2.05/1.27  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_210])).
% 2.05/1.27  tff(c_219, plain, (![B_55]: (r2_hidden(B_55, '#skF_4') | ~r2_hidden(B_55, '#skF_3'))), inference(splitRight, [status(thm)], [c_154])).
% 2.05/1.27  tff(c_275, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_3', B_59), '#skF_4') | r1_tarski('#skF_3', B_59))), inference(resolution, [status(thm)], [c_8, c_219])).
% 2.05/1.27  tff(c_289, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_275, c_6])).
% 2.05/1.27  tff(c_293, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_289, c_12])).
% 2.05/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.27  tff(c_297, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_293, c_2])).
% 2.05/1.27  tff(c_309, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_297])).
% 2.05/1.27  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_309])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 63
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 2
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 4
% 2.05/1.27  #Demod        : 4
% 2.05/1.27  #Tautology    : 23
% 2.05/1.27  #SimpNegUnit  : 6
% 2.05/1.27  #BackRed      : 2
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.27  Preprocessing        : 0.29
% 2.05/1.27  Parsing              : 0.15
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.22
% 2.05/1.27  Inferencing          : 0.09
% 2.05/1.27  Reduction            : 0.06
% 2.05/1.27  Demodulation         : 0.03
% 2.05/1.27  BG Simplification    : 0.02
% 2.05/1.27  Subsumption          : 0.05
% 2.05/1.27  Abstraction          : 0.01
% 2.05/1.27  MUC search           : 0.00
% 2.05/1.27  Cooper               : 0.00
% 2.05/1.27  Total                : 0.54
% 2.05/1.27  Index Insertion      : 0.00
% 2.05/1.27  Index Deletion       : 0.00
% 2.05/1.27  Index Matching       : 0.00
% 2.05/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
