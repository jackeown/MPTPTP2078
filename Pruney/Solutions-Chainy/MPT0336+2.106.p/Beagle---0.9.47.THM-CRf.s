%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   48 (  67 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 116 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_142,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_xboole_0(A_52,C_53)
      | ~ r1_xboole_0(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_378,plain,(
    ! [A_95,B_96,A_97] :
      ( r1_xboole_0(A_95,B_96)
      | ~ r1_tarski(A_95,k1_tarski(A_97))
      | r2_hidden(A_97,B_96) ) ),
    inference(resolution,[status(thm)],[c_26,c_142])).

tff(c_382,plain,(
    ! [B_98] :
      ( r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),B_98)
      | r2_hidden('#skF_5',B_98) ) ),
    inference(resolution,[status(thm)],[c_34,c_378])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( ~ r1_xboole_0(k3_xboole_0(A_16,B_17),B_17)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_404,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_382,c_20])).

tff(c_407,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_104,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,B_47)
      | ~ r2_hidden(C_48,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [C_48] :
      ( ~ r2_hidden(C_48,'#skF_3')
      | ~ r2_hidden(C_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_415,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_407,c_116])).

tff(c_421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_415])).

tff(c_422,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_447,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_422,c_2])).

tff(c_44,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_189,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r1_xboole_0(A_57,C_58)
      | ~ r1_xboole_0(A_57,B_59)
      | r1_xboole_0(A_57,k2_xboole_0(B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_603,plain,(
    ! [B_129,C_130,A_131] :
      ( r1_xboole_0(k2_xboole_0(B_129,C_130),A_131)
      | ~ r1_xboole_0(A_131,C_130)
      | ~ r1_xboole_0(A_131,B_129) ) ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_28,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_620,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_603,c_28])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_47,c_620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.45  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.70/1.45  
% 2.70/1.45  %Foreground sorts:
% 2.70/1.45  
% 2.70/1.45  
% 2.70/1.45  %Background operators:
% 2.70/1.45  
% 2.70/1.45  
% 2.70/1.45  %Foreground operators:
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.70/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.45  
% 3.03/1.46  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.03/1.46  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.03/1.46  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.03/1.46  tff(f_77, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.03/1.46  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.03/1.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.03/1.46  tff(f_71, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.03/1.46  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.03/1.46  tff(c_34, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.03/1.46  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.03/1.46  tff(c_142, plain, (![A_52, C_53, B_54]: (r1_xboole_0(A_52, C_53) | ~r1_xboole_0(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.03/1.46  tff(c_378, plain, (![A_95, B_96, A_97]: (r1_xboole_0(A_95, B_96) | ~r1_tarski(A_95, k1_tarski(A_97)) | r2_hidden(A_97, B_96))), inference(resolution, [status(thm)], [c_26, c_142])).
% 3.03/1.46  tff(c_382, plain, (![B_98]: (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), B_98) | r2_hidden('#skF_5', B_98))), inference(resolution, [status(thm)], [c_34, c_378])).
% 3.03/1.46  tff(c_20, plain, (![A_16, B_17]: (~r1_xboole_0(k3_xboole_0(A_16, B_17), B_17) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.03/1.46  tff(c_404, plain, (r1_xboole_0('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_382, c_20])).
% 3.03/1.46  tff(c_407, plain, (r2_hidden('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_404])).
% 3.03/1.46  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.03/1.46  tff(c_104, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, B_47) | ~r2_hidden(C_48, A_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.03/1.46  tff(c_116, plain, (![C_48]: (~r2_hidden(C_48, '#skF_3') | ~r2_hidden(C_48, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_104])).
% 3.03/1.46  tff(c_415, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_407, c_116])).
% 3.03/1.46  tff(c_421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_415])).
% 3.03/1.46  tff(c_422, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_404])).
% 3.03/1.46  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.46  tff(c_447, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_422, c_2])).
% 3.03/1.46  tff(c_44, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.03/1.46  tff(c_47, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_44])).
% 3.03/1.46  tff(c_189, plain, (![A_57, C_58, B_59]: (~r1_xboole_0(A_57, C_58) | ~r1_xboole_0(A_57, B_59) | r1_xboole_0(A_57, k2_xboole_0(B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.46  tff(c_603, plain, (![B_129, C_130, A_131]: (r1_xboole_0(k2_xboole_0(B_129, C_130), A_131) | ~r1_xboole_0(A_131, C_130) | ~r1_xboole_0(A_131, B_129))), inference(resolution, [status(thm)], [c_189, c_2])).
% 3.03/1.46  tff(c_28, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.03/1.46  tff(c_620, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_603, c_28])).
% 3.03/1.46  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_47, c_620])).
% 3.03/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  Inference rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Ref     : 0
% 3.03/1.46  #Sup     : 138
% 3.03/1.46  #Fact    : 0
% 3.03/1.46  #Define  : 0
% 3.03/1.46  #Split   : 4
% 3.03/1.46  #Chain   : 0
% 3.03/1.46  #Close   : 0
% 3.03/1.46  
% 3.03/1.46  Ordering : KBO
% 3.03/1.46  
% 3.03/1.46  Simplification rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Subsume      : 14
% 3.03/1.46  #Demod        : 10
% 3.03/1.46  #Tautology    : 17
% 3.03/1.46  #SimpNegUnit  : 0
% 3.03/1.46  #BackRed      : 0
% 3.03/1.46  
% 3.03/1.46  #Partial instantiations: 0
% 3.03/1.46  #Strategies tried      : 1
% 3.03/1.46  
% 3.03/1.46  Timing (in seconds)
% 3.03/1.46  ----------------------
% 3.03/1.47  Preprocessing        : 0.32
% 3.03/1.47  Parsing              : 0.18
% 3.03/1.47  CNF conversion       : 0.02
% 3.03/1.47  Main loop            : 0.35
% 3.03/1.47  Inferencing          : 0.14
% 3.03/1.47  Reduction            : 0.08
% 3.03/1.47  Demodulation         : 0.06
% 3.03/1.47  BG Simplification    : 0.02
% 3.03/1.47  Subsumption          : 0.09
% 3.03/1.47  Abstraction          : 0.02
% 3.03/1.47  MUC search           : 0.00
% 3.03/1.47  Cooper               : 0.00
% 3.03/1.47  Total                : 0.70
% 3.03/1.47  Index Insertion      : 0.00
% 3.03/1.47  Index Deletion       : 0.00
% 3.03/1.47  Index Matching       : 0.00
% 3.03/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
