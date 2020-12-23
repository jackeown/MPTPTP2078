%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:06 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 171 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 ( 529 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k1_relat_1(A_12),k1_relat_1(B_14))
      | ~ r1_tarski(A_12,B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden('#skF_1'(A_18,B_19),B_19)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_54,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden('#skF_2'(A_34,B_35,C_36),k1_relat_1(C_36))
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_34,B_35,C_36,B_2] :
      ( r2_hidden('#skF_2'(A_34,B_35,C_36),B_2)
      | ~ r1_tarski(k1_relat_1(C_36),B_2)
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden(k4_tarski('#skF_2'(A_6,B_7,C_8),A_6),C_8)
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),k1_relat_1(C_8))
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_67,C_68,B_69,D_70] :
      ( r2_hidden(A_67,k9_relat_1(C_68,B_69))
      | ~ r2_hidden(D_70,B_69)
      | ~ r2_hidden(k4_tarski(D_70,A_67),C_68)
      | ~ r2_hidden(D_70,k1_relat_1(C_68))
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_444,plain,(
    ! [C_170,C_173,A_169,A_172,B_171] :
      ( r2_hidden(A_169,k9_relat_1(C_173,k1_relat_1(C_170)))
      | ~ r2_hidden(k4_tarski('#skF_2'(A_172,B_171,C_170),A_169),C_173)
      | ~ r2_hidden('#skF_2'(A_172,B_171,C_170),k1_relat_1(C_173))
      | ~ v1_relat_1(C_173)
      | ~ r2_hidden(A_172,k9_relat_1(C_170,B_171))
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_14,c_147])).

tff(c_463,plain,(
    ! [A_174,C_175,B_176] :
      ( r2_hidden(A_174,k9_relat_1(C_175,k1_relat_1(C_175)))
      | ~ r2_hidden('#skF_2'(A_174,B_176,C_175),k1_relat_1(C_175))
      | ~ r2_hidden(A_174,k9_relat_1(C_175,B_176))
      | ~ v1_relat_1(C_175) ) ),
    inference(resolution,[status(thm)],[c_12,c_444])).

tff(c_475,plain,(
    ! [A_34,C_36,B_35] :
      ( r2_hidden(A_34,k9_relat_1(C_36,k1_relat_1(C_36)))
      | ~ r1_tarski(k1_relat_1(C_36),k1_relat_1(C_36))
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(resolution,[status(thm)],[c_57,c_463])).

tff(c_495,plain,(
    ! [A_177,C_178,B_179] :
      ( r2_hidden(A_177,k9_relat_1(C_178,k1_relat_1(C_178)))
      | ~ r2_hidden(A_177,k9_relat_1(C_178,B_179))
      | ~ v1_relat_1(C_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_475])).

tff(c_539,plain,(
    ! [C_178,B_179,B_2] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_178,B_179),B_2),k9_relat_1(C_178,k1_relat_1(C_178)))
      | ~ v1_relat_1(C_178)
      | r1_tarski(k9_relat_1(C_178,B_179),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_495])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_2'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(A_31,k9_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_31,B_32,C_33,B_2] :
      ( r2_hidden('#skF_2'(A_31,B_32,C_33),B_2)
      | ~ r1_tarski(B_32,B_2)
      | ~ r2_hidden(A_31,k9_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_80,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden(k4_tarski('#skF_2'(A_43,B_44,C_45),A_43),C_45)
      | ~ r2_hidden(A_43,k9_relat_1(C_45,B_44))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [A_43,B_44,C_45,B_2] :
      ( r2_hidden(k4_tarski('#skF_2'(A_43,B_44,C_45),A_43),B_2)
      | ~ r1_tarski(C_45,B_2)
      | ~ r2_hidden(A_43,k9_relat_1(C_45,B_44))
      | ~ v1_relat_1(C_45) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_354,plain,(
    ! [A_145,B_147,A_148,C_149,C_146] :
      ( r2_hidden(A_145,k9_relat_1(C_149,B_147))
      | ~ r2_hidden(k4_tarski('#skF_2'(A_148,B_147,C_146),A_145),C_149)
      | ~ r2_hidden('#skF_2'(A_148,B_147,C_146),k1_relat_1(C_149))
      | ~ v1_relat_1(C_149)
      | ~ r2_hidden(A_148,k9_relat_1(C_146,B_147))
      | ~ v1_relat_1(C_146) ) ),
    inference(resolution,[status(thm)],[c_10,c_147])).

tff(c_627,plain,(
    ! [A_215,B_216,B_217,C_218] :
      ( r2_hidden(A_215,k9_relat_1(B_216,B_217))
      | ~ r2_hidden('#skF_2'(A_215,B_217,C_218),k1_relat_1(B_216))
      | ~ v1_relat_1(B_216)
      | ~ r1_tarski(C_218,B_216)
      | ~ r2_hidden(A_215,k9_relat_1(C_218,B_217))
      | ~ v1_relat_1(C_218) ) ),
    inference(resolution,[status(thm)],[c_83,c_354])).

tff(c_709,plain,(
    ! [A_222,B_223,B_224,C_225] :
      ( r2_hidden(A_222,k9_relat_1(B_223,B_224))
      | ~ v1_relat_1(B_223)
      | ~ r1_tarski(C_225,B_223)
      | ~ r1_tarski(B_224,k1_relat_1(B_223))
      | ~ r2_hidden(A_222,k9_relat_1(C_225,B_224))
      | ~ v1_relat_1(C_225) ) ),
    inference(resolution,[status(thm)],[c_53,c_627])).

tff(c_721,plain,(
    ! [A_222,B_224] :
      ( r2_hidden(A_222,k9_relat_1('#skF_5',B_224))
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(B_224,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_222,k9_relat_1('#skF_4',B_224))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_709])).

tff(c_732,plain,(
    ! [A_226,B_227] :
      ( r2_hidden(A_226,k9_relat_1('#skF_5',B_227))
      | ~ r1_tarski(B_227,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_226,k9_relat_1('#skF_4',B_227)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_721])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_924,plain,(
    ! [A_235,B_236] :
      ( r1_tarski(A_235,k9_relat_1('#skF_5',B_236))
      | ~ r1_tarski(B_236,k1_relat_1('#skF_5'))
      | ~ r2_hidden('#skF_1'(A_235,k9_relat_1('#skF_5',B_236)),k9_relat_1('#skF_4',B_236)) ) ),
    inference(resolution,[status(thm)],[c_732,c_4])).

tff(c_928,plain,(
    ! [B_179] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_4')
      | r1_tarski(k9_relat_1('#skF_4',B_179),k9_relat_1('#skF_5',k1_relat_1('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_539,c_924])).

tff(c_943,plain,(
    ! [B_179] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | r1_tarski(k9_relat_1('#skF_4',B_179),k9_relat_1('#skF_5',k1_relat_1('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_928])).

tff(c_1025,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_943])).

tff(c_1028,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1025])).

tff(c_1032,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_1028])).

tff(c_1034,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_943])).

tff(c_3288,plain,(
    ! [A_361,B_362,B_363,C_364] :
      ( r2_hidden(A_361,k9_relat_1(B_362,B_363))
      | ~ v1_relat_1(B_362)
      | ~ r1_tarski(C_364,B_362)
      | ~ r1_tarski(k1_relat_1(C_364),k1_relat_1(B_362))
      | ~ r2_hidden(A_361,k9_relat_1(C_364,B_363))
      | ~ v1_relat_1(C_364) ) ),
    inference(resolution,[status(thm)],[c_57,c_627])).

tff(c_3299,plain,(
    ! [A_361,B_363] :
      ( r2_hidden(A_361,k9_relat_1('#skF_5',B_363))
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_4','#skF_5')
      | ~ r2_hidden(A_361,k9_relat_1('#skF_4',B_363))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1034,c_3288])).

tff(c_3322,plain,(
    ! [A_365,B_366] :
      ( r2_hidden(A_365,k9_relat_1('#skF_5',B_366))
      | ~ r2_hidden(A_365,k9_relat_1('#skF_4',B_366)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_24,c_3299])).

tff(c_4119,plain,(
    ! [A_392,B_393] :
      ( r1_tarski(A_392,k9_relat_1('#skF_5',B_393))
      | ~ r2_hidden('#skF_1'(A_392,k9_relat_1('#skF_5',B_393)),k9_relat_1('#skF_4',B_393)) ) ),
    inference(resolution,[status(thm)],[c_3322,c_4])).

tff(c_4160,plain,(
    ! [B_393] : r1_tarski(k9_relat_1('#skF_4',B_393),k9_relat_1('#skF_5',B_393)) ),
    inference(resolution,[status(thm)],[c_6,c_4119])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k9_relat_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4160,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:24:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.96/2.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.44  
% 6.96/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.44  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 6.96/2.44  
% 6.96/2.44  %Foreground sorts:
% 6.96/2.44  
% 6.96/2.44  
% 6.96/2.44  %Background operators:
% 6.96/2.44  
% 6.96/2.44  
% 6.96/2.44  %Foreground operators:
% 6.96/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.96/2.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.96/2.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.96/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.96/2.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.96/2.44  tff('#skF_5', type, '#skF_5': $i).
% 6.96/2.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.96/2.44  tff('#skF_3', type, '#skF_3': $i).
% 6.96/2.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.96/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.96/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.96/2.44  tff('#skF_4', type, '#skF_4': $i).
% 6.96/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.96/2.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.96/2.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.96/2.44  
% 6.96/2.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.96/2.46  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 6.96/2.46  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 6.96/2.46  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 6.96/2.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.96/2.46  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.96/2.46  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.96/2.46  tff(c_24, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.96/2.46  tff(c_18, plain, (![A_12, B_14]: (r1_tarski(k1_relat_1(A_12), k1_relat_1(B_14)) | ~r1_tarski(A_12, B_14) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.96/2.46  tff(c_28, plain, (![A_18, B_19]: (~r2_hidden('#skF_1'(A_18, B_19), B_19) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.96/2.46  tff(c_33, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_28])).
% 6.96/2.46  tff(c_54, plain, (![A_34, B_35, C_36]: (r2_hidden('#skF_2'(A_34, B_35, C_36), k1_relat_1(C_36)) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.96/2.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.96/2.46  tff(c_57, plain, (![A_34, B_35, C_36, B_2]: (r2_hidden('#skF_2'(A_34, B_35, C_36), B_2) | ~r1_tarski(k1_relat_1(C_36), B_2) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(resolution, [status(thm)], [c_54, c_2])).
% 6.96/2.46  tff(c_12, plain, (![A_6, B_7, C_8]: (r2_hidden(k4_tarski('#skF_2'(A_6, B_7, C_8), A_6), C_8) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.96/2.46  tff(c_14, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), k1_relat_1(C_8)) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.96/2.46  tff(c_147, plain, (![A_67, C_68, B_69, D_70]: (r2_hidden(A_67, k9_relat_1(C_68, B_69)) | ~r2_hidden(D_70, B_69) | ~r2_hidden(k4_tarski(D_70, A_67), C_68) | ~r2_hidden(D_70, k1_relat_1(C_68)) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.96/2.46  tff(c_444, plain, (![C_170, C_173, A_169, A_172, B_171]: (r2_hidden(A_169, k9_relat_1(C_173, k1_relat_1(C_170))) | ~r2_hidden(k4_tarski('#skF_2'(A_172, B_171, C_170), A_169), C_173) | ~r2_hidden('#skF_2'(A_172, B_171, C_170), k1_relat_1(C_173)) | ~v1_relat_1(C_173) | ~r2_hidden(A_172, k9_relat_1(C_170, B_171)) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_14, c_147])).
% 6.96/2.46  tff(c_463, plain, (![A_174, C_175, B_176]: (r2_hidden(A_174, k9_relat_1(C_175, k1_relat_1(C_175))) | ~r2_hidden('#skF_2'(A_174, B_176, C_175), k1_relat_1(C_175)) | ~r2_hidden(A_174, k9_relat_1(C_175, B_176)) | ~v1_relat_1(C_175))), inference(resolution, [status(thm)], [c_12, c_444])).
% 6.96/2.46  tff(c_475, plain, (![A_34, C_36, B_35]: (r2_hidden(A_34, k9_relat_1(C_36, k1_relat_1(C_36))) | ~r1_tarski(k1_relat_1(C_36), k1_relat_1(C_36)) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(resolution, [status(thm)], [c_57, c_463])).
% 6.96/2.46  tff(c_495, plain, (![A_177, C_178, B_179]: (r2_hidden(A_177, k9_relat_1(C_178, k1_relat_1(C_178))) | ~r2_hidden(A_177, k9_relat_1(C_178, B_179)) | ~v1_relat_1(C_178))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_475])).
% 6.96/2.46  tff(c_539, plain, (![C_178, B_179, B_2]: (r2_hidden('#skF_1'(k9_relat_1(C_178, B_179), B_2), k9_relat_1(C_178, k1_relat_1(C_178))) | ~v1_relat_1(C_178) | r1_tarski(k9_relat_1(C_178, B_179), B_2))), inference(resolution, [status(thm)], [c_6, c_495])).
% 6.96/2.46  tff(c_50, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_2'(A_31, B_32, C_33), B_32) | ~r2_hidden(A_31, k9_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.96/2.46  tff(c_53, plain, (![A_31, B_32, C_33, B_2]: (r2_hidden('#skF_2'(A_31, B_32, C_33), B_2) | ~r1_tarski(B_32, B_2) | ~r2_hidden(A_31, k9_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(resolution, [status(thm)], [c_50, c_2])).
% 6.96/2.46  tff(c_80, plain, (![A_43, B_44, C_45]: (r2_hidden(k4_tarski('#skF_2'(A_43, B_44, C_45), A_43), C_45) | ~r2_hidden(A_43, k9_relat_1(C_45, B_44)) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.96/2.46  tff(c_83, plain, (![A_43, B_44, C_45, B_2]: (r2_hidden(k4_tarski('#skF_2'(A_43, B_44, C_45), A_43), B_2) | ~r1_tarski(C_45, B_2) | ~r2_hidden(A_43, k9_relat_1(C_45, B_44)) | ~v1_relat_1(C_45))), inference(resolution, [status(thm)], [c_80, c_2])).
% 6.96/2.46  tff(c_10, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.96/2.46  tff(c_354, plain, (![A_145, B_147, A_148, C_149, C_146]: (r2_hidden(A_145, k9_relat_1(C_149, B_147)) | ~r2_hidden(k4_tarski('#skF_2'(A_148, B_147, C_146), A_145), C_149) | ~r2_hidden('#skF_2'(A_148, B_147, C_146), k1_relat_1(C_149)) | ~v1_relat_1(C_149) | ~r2_hidden(A_148, k9_relat_1(C_146, B_147)) | ~v1_relat_1(C_146))), inference(resolution, [status(thm)], [c_10, c_147])).
% 6.96/2.46  tff(c_627, plain, (![A_215, B_216, B_217, C_218]: (r2_hidden(A_215, k9_relat_1(B_216, B_217)) | ~r2_hidden('#skF_2'(A_215, B_217, C_218), k1_relat_1(B_216)) | ~v1_relat_1(B_216) | ~r1_tarski(C_218, B_216) | ~r2_hidden(A_215, k9_relat_1(C_218, B_217)) | ~v1_relat_1(C_218))), inference(resolution, [status(thm)], [c_83, c_354])).
% 6.96/2.46  tff(c_709, plain, (![A_222, B_223, B_224, C_225]: (r2_hidden(A_222, k9_relat_1(B_223, B_224)) | ~v1_relat_1(B_223) | ~r1_tarski(C_225, B_223) | ~r1_tarski(B_224, k1_relat_1(B_223)) | ~r2_hidden(A_222, k9_relat_1(C_225, B_224)) | ~v1_relat_1(C_225))), inference(resolution, [status(thm)], [c_53, c_627])).
% 6.96/2.46  tff(c_721, plain, (![A_222, B_224]: (r2_hidden(A_222, k9_relat_1('#skF_5', B_224)) | ~v1_relat_1('#skF_5') | ~r1_tarski(B_224, k1_relat_1('#skF_5')) | ~r2_hidden(A_222, k9_relat_1('#skF_4', B_224)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_709])).
% 6.96/2.46  tff(c_732, plain, (![A_226, B_227]: (r2_hidden(A_226, k9_relat_1('#skF_5', B_227)) | ~r1_tarski(B_227, k1_relat_1('#skF_5')) | ~r2_hidden(A_226, k9_relat_1('#skF_4', B_227)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_721])).
% 6.96/2.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.96/2.46  tff(c_924, plain, (![A_235, B_236]: (r1_tarski(A_235, k9_relat_1('#skF_5', B_236)) | ~r1_tarski(B_236, k1_relat_1('#skF_5')) | ~r2_hidden('#skF_1'(A_235, k9_relat_1('#skF_5', B_236)), k9_relat_1('#skF_4', B_236)))), inference(resolution, [status(thm)], [c_732, c_4])).
% 6.96/2.46  tff(c_928, plain, (![B_179]: (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_4') | r1_tarski(k9_relat_1('#skF_4', B_179), k9_relat_1('#skF_5', k1_relat_1('#skF_4'))))), inference(resolution, [status(thm)], [c_539, c_924])).
% 6.96/2.46  tff(c_943, plain, (![B_179]: (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | r1_tarski(k9_relat_1('#skF_4', B_179), k9_relat_1('#skF_5', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_928])).
% 6.96/2.46  tff(c_1025, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_943])).
% 6.96/2.46  tff(c_1028, plain, (~r1_tarski('#skF_4', '#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_1025])).
% 6.96/2.46  tff(c_1032, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_1028])).
% 6.96/2.46  tff(c_1034, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_943])).
% 6.96/2.46  tff(c_3288, plain, (![A_361, B_362, B_363, C_364]: (r2_hidden(A_361, k9_relat_1(B_362, B_363)) | ~v1_relat_1(B_362) | ~r1_tarski(C_364, B_362) | ~r1_tarski(k1_relat_1(C_364), k1_relat_1(B_362)) | ~r2_hidden(A_361, k9_relat_1(C_364, B_363)) | ~v1_relat_1(C_364))), inference(resolution, [status(thm)], [c_57, c_627])).
% 6.96/2.46  tff(c_3299, plain, (![A_361, B_363]: (r2_hidden(A_361, k9_relat_1('#skF_5', B_363)) | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_4', '#skF_5') | ~r2_hidden(A_361, k9_relat_1('#skF_4', B_363)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1034, c_3288])).
% 6.96/2.46  tff(c_3322, plain, (![A_365, B_366]: (r2_hidden(A_365, k9_relat_1('#skF_5', B_366)) | ~r2_hidden(A_365, k9_relat_1('#skF_4', B_366)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_24, c_3299])).
% 6.96/2.46  tff(c_4119, plain, (![A_392, B_393]: (r1_tarski(A_392, k9_relat_1('#skF_5', B_393)) | ~r2_hidden('#skF_1'(A_392, k9_relat_1('#skF_5', B_393)), k9_relat_1('#skF_4', B_393)))), inference(resolution, [status(thm)], [c_3322, c_4])).
% 6.96/2.46  tff(c_4160, plain, (![B_393]: (r1_tarski(k9_relat_1('#skF_4', B_393), k9_relat_1('#skF_5', B_393)))), inference(resolution, [status(thm)], [c_6, c_4119])).
% 6.96/2.46  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k9_relat_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.96/2.46  tff(c_4164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4160, c_20])).
% 6.96/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.46  
% 6.96/2.46  Inference rules
% 6.96/2.46  ----------------------
% 6.96/2.46  #Ref     : 0
% 6.96/2.46  #Sup     : 988
% 6.96/2.46  #Fact    : 0
% 6.96/2.46  #Define  : 0
% 6.96/2.46  #Split   : 12
% 6.96/2.46  #Chain   : 0
% 6.96/2.46  #Close   : 0
% 6.96/2.46  
% 6.96/2.46  Ordering : KBO
% 6.96/2.46  
% 6.96/2.46  Simplification rules
% 6.96/2.46  ----------------------
% 6.96/2.46  #Subsume      : 212
% 6.96/2.46  #Demod        : 199
% 6.96/2.46  #Tautology    : 12
% 6.96/2.46  #SimpNegUnit  : 0
% 6.96/2.46  #BackRed      : 1
% 6.96/2.46  
% 6.96/2.46  #Partial instantiations: 0
% 6.96/2.46  #Strategies tried      : 1
% 6.96/2.46  
% 6.96/2.46  Timing (in seconds)
% 6.96/2.46  ----------------------
% 6.96/2.46  Preprocessing        : 0.27
% 6.96/2.46  Parsing              : 0.15
% 6.96/2.46  CNF conversion       : 0.02
% 6.96/2.46  Main loop            : 1.38
% 6.96/2.46  Inferencing          : 0.37
% 6.96/2.46  Reduction            : 0.31
% 6.96/2.46  Demodulation         : 0.19
% 6.96/2.46  BG Simplification    : 0.04
% 6.96/2.46  Subsumption          : 0.57
% 6.96/2.46  Abstraction          : 0.05
% 6.96/2.46  MUC search           : 0.00
% 6.96/2.46  Cooper               : 0.00
% 6.96/2.46  Total                : 1.68
% 6.96/2.46  Index Insertion      : 0.00
% 6.96/2.46  Index Deletion       : 0.00
% 6.96/2.46  Index Matching       : 0.00
% 6.96/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
