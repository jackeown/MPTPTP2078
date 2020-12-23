%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:50 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  69 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

tff(f_35,axiom,(
    ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [A_49,B_50] :
      ( v1_relat_1(k3_xboole_0(A_49,B_50))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47])).

tff(c_52,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_176,plain,(
    ! [A_84,B_85] :
      ( r2_hidden(k4_tarski('#skF_1'(A_84,B_85),'#skF_2'(A_84,B_85)),B_85)
      | r2_hidden(k4_tarski('#skF_3'(A_84,B_85),'#skF_4'(A_84,B_85)),A_84)
      | B_85 = A_84
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [B_44,C_45] : ~ r2_hidden(k4_tarski(B_44,C_45),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_204,plain,(
    ! [B_85] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_5',B_85),'#skF_2'('#skF_5',B_85)),B_85)
      | B_85 = '#skF_5'
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_176,c_36])).

tff(c_215,plain,(
    ! [B_86] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_5',B_86),'#skF_2'('#skF_5',B_86)),B_86)
      | B_86 = '#skF_5'
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_204])).

tff(c_74,plain,(
    ! [A_59,B_60] : k4_enumset1(A_59,A_59,A_59,A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_17] : k4_enumset1(A_17,A_17,A_17,A_17,A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [B_61] : k2_tarski(B_61,B_61) = k1_tarski(B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_10])).

tff(c_12,plain,(
    ! [A_18,B_19] : k4_xboole_0(k1_tarski(A_18),k2_tarski(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [B_65] : k4_xboole_0(k1_tarski(B_65),k1_tarski(B_65)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_12])).

tff(c_16,plain,(
    ! [C_22,B_21] : ~ r2_hidden(C_22,k4_xboole_0(B_21,k1_tarski(C_22))) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125,plain,(
    ! [B_65] : ~ r2_hidden(B_65,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_16])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_215,c_125])).

tff(c_235,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_223])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:46:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.30  
% 2.01/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.30  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.01/1.30  
% 2.01/1.30  %Foreground sorts:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Background operators:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Foreground operators:
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.01/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.01/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.01/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.01/1.30  
% 2.17/1.31  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 2.17/1.31  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.17/1.31  tff(f_60, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.17/1.31  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_relat_1)).
% 2.17/1.31  tff(f_33, axiom, (![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_enumset1)).
% 2.17/1.31  tff(f_35, axiom, (![A]: (k4_enumset1(A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_enumset1)).
% 2.17/1.31  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.17/1.31  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.17/1.31  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.31  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.31  tff(c_47, plain, (![A_49, B_50]: (v1_relat_1(k3_xboole_0(A_49, B_50)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.31  tff(c_50, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_47])).
% 2.17/1.31  tff(c_52, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_50])).
% 2.17/1.31  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.31  tff(c_55, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38])).
% 2.17/1.31  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_50])).
% 2.17/1.31  tff(c_176, plain, (![A_84, B_85]: (r2_hidden(k4_tarski('#skF_1'(A_84, B_85), '#skF_2'(A_84, B_85)), B_85) | r2_hidden(k4_tarski('#skF_3'(A_84, B_85), '#skF_4'(A_84, B_85)), A_84) | B_85=A_84 | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.31  tff(c_36, plain, (![B_44, C_45]: (~r2_hidden(k4_tarski(B_44, C_45), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.31  tff(c_204, plain, (![B_85]: (r2_hidden(k4_tarski('#skF_1'('#skF_5', B_85), '#skF_2'('#skF_5', B_85)), B_85) | B_85='#skF_5' | ~v1_relat_1(B_85) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_176, c_36])).
% 2.17/1.31  tff(c_215, plain, (![B_86]: (r2_hidden(k4_tarski('#skF_1'('#skF_5', B_86), '#skF_2'('#skF_5', B_86)), B_86) | B_86='#skF_5' | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_204])).
% 2.17/1.31  tff(c_74, plain, (![A_59, B_60]: (k4_enumset1(A_59, A_59, A_59, A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.31  tff(c_10, plain, (![A_17]: (k4_enumset1(A_17, A_17, A_17, A_17, A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.31  tff(c_90, plain, (![B_61]: (k2_tarski(B_61, B_61)=k1_tarski(B_61))), inference(superposition, [status(thm), theory('equality')], [c_74, c_10])).
% 2.17/1.31  tff(c_12, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), k2_tarski(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.31  tff(c_114, plain, (![B_65]: (k4_xboole_0(k1_tarski(B_65), k1_tarski(B_65))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_12])).
% 2.17/1.31  tff(c_16, plain, (![C_22, B_21]: (~r2_hidden(C_22, k4_xboole_0(B_21, k1_tarski(C_22))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.31  tff(c_125, plain, (![B_65]: (~r2_hidden(B_65, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_114, c_16])).
% 2.17/1.31  tff(c_223, plain, (k1_xboole_0='#skF_5' | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_215, c_125])).
% 2.17/1.31  tff(c_235, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_223])).
% 2.17/1.31  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_235])).
% 2.17/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  Inference rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Ref     : 0
% 2.17/1.31  #Sup     : 39
% 2.17/1.31  #Fact    : 0
% 2.17/1.31  #Define  : 0
% 2.17/1.31  #Split   : 1
% 2.17/1.31  #Chain   : 0
% 2.17/1.31  #Close   : 0
% 2.17/1.31  
% 2.17/1.31  Ordering : KBO
% 2.17/1.31  
% 2.17/1.31  Simplification rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Subsume      : 4
% 2.17/1.31  #Demod        : 6
% 2.17/1.31  #Tautology    : 21
% 2.17/1.31  #SimpNegUnit  : 4
% 2.17/1.31  #BackRed      : 1
% 2.17/1.31  
% 2.17/1.31  #Partial instantiations: 0
% 2.17/1.31  #Strategies tried      : 1
% 2.17/1.31  
% 2.17/1.31  Timing (in seconds)
% 2.17/1.31  ----------------------
% 2.17/1.31  Preprocessing        : 0.30
% 2.17/1.31  Parsing              : 0.15
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.17
% 2.17/1.31  Inferencing          : 0.07
% 2.17/1.31  Reduction            : 0.05
% 2.17/1.31  Demodulation         : 0.03
% 2.17/1.31  BG Simplification    : 0.01
% 2.17/1.31  Subsumption          : 0.03
% 2.17/1.32  Abstraction          : 0.01
% 2.17/1.32  MUC search           : 0.00
% 2.17/1.32  Cooper               : 0.00
% 2.17/1.32  Total                : 0.49
% 2.17/1.32  Index Insertion      : 0.00
% 2.17/1.32  Index Deletion       : 0.00
% 2.17/1.32  Index Matching       : 0.00
% 2.17/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
