%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:29 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 301 expanded)
%              Number of leaves         :   29 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 820 expanded)
%              Number of equality atoms :   53 ( 333 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( k1_relat_1(A) = k1_relat_1(B)
                  & ! [D] :
                      ( r2_hidden(D,C)
                     => k1_funct_1(A,D) = k1_funct_1(B,D) ) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ! [C] :
              ( ( r1_tarski(C,k1_relat_1(A))
                & r1_tarski(C,k1_relat_1(B)) )
             => ( k7_relat_1(A,C) = k7_relat_1(B,C)
              <=> ! [D] :
                    ( r2_hidden(D,C)
                   => k1_funct_1(A,D) = k1_funct_1(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_36,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    k1_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_136,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(k1_relat_1(B_68),A_69) = k1_relat_1(k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_162,plain,(
    ! [A_69] :
      ( k3_xboole_0(k1_relat_1('#skF_3'),A_69) = k1_relat_1(k7_relat_1('#skF_2',A_69))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_136])).

tff(c_171,plain,(
    ! [A_73] : k3_xboole_0(k1_relat_1('#skF_3'),A_73) = k1_relat_1(k7_relat_1('#skF_2',A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_162])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k1_relat_1(B_17),A_16) = k1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_177,plain,(
    ! [A_73] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_73)) = k1_relat_1(k7_relat_1('#skF_3',A_73))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_22])).

tff(c_201,plain,(
    ! [A_73] : k1_relat_1(k7_relat_1('#skF_2',A_73)) = k1_relat_1(k7_relat_1('#skF_3',A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_177])).

tff(c_125,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_66,A_67)),k1_relat_1(B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_131,plain,(
    ! [A_67] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_67)),k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_125])).

tff(c_135,plain,(
    ! [A_67] : r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_67)),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_131])).

tff(c_405,plain,(
    ! [A_67] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_67)),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_135])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_198,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_relat_1('#skF_3')) = k1_relat_1(k7_relat_1('#skF_2',A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_171])).

tff(c_403,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_relat_1('#skF_3')) = k1_relat_1(k7_relat_1('#skF_3',A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_198])).

tff(c_26,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_159,plain,(
    ! [A_10,A_69] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_10),A_69)) = k3_xboole_0(A_10,A_69)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_166,plain,(
    ! [A_10,A_69] : k1_relat_1(k7_relat_1(k6_relat_1(A_10),A_69)) = k3_xboole_0(A_10,A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_159])).

tff(c_1250,plain,(
    ! [A_123,B_124] :
      ( k7_relat_1(A_123,k1_relat_1(k7_relat_1(B_124,k1_relat_1(A_123)))) = k7_relat_1(A_123,k1_relat_1(B_124))
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1321,plain,(
    ! [A_123,A_10] :
      ( k7_relat_1(A_123,k3_xboole_0(A_10,k1_relat_1(A_123))) = k7_relat_1(A_123,k1_relat_1(k6_relat_1(A_10)))
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_1250])).

tff(c_4693,plain,(
    ! [A_204,A_205] :
      ( k7_relat_1(A_204,k3_xboole_0(A_205,k1_relat_1(A_204))) = k7_relat_1(A_204,A_205)
      | ~ v1_relat_1(A_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10,c_1321])).

tff(c_4827,plain,(
    ! [A_1] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_1))) = k7_relat_1('#skF_3',A_1)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_4693])).

tff(c_4891,plain,(
    ! [A_1] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_1))) = k7_relat_1('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4827])).

tff(c_1327,plain,(
    ! [B_124] :
      ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_124,k1_relat_1('#skF_3')))) = k7_relat_1('#skF_2',k1_relat_1(B_124))
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1250])).

tff(c_1622,plain,(
    ! [B_129] :
      ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_129,k1_relat_1('#skF_3')))) = k7_relat_1('#skF_2',k1_relat_1(B_129))
      | ~ v1_relat_1(B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1327])).

tff(c_1657,plain,(
    ! [A_10] :
      ( k7_relat_1('#skF_2',k3_xboole_0(A_10,k1_relat_1('#skF_3'))) = k7_relat_1('#skF_2',k1_relat_1(k6_relat_1(A_10)))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_1622])).

tff(c_1676,plain,(
    ! [A_10] : k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',A_10))) = k7_relat_1('#skF_2',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_403,c_10,c_1657])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1776,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden('#skF_1'(A_133,B_134,C_135),C_135)
      | k7_relat_1(B_134,C_135) = k7_relat_1(A_133,C_135)
      | ~ r1_tarski(C_135,k1_relat_1(B_134))
      | ~ r1_tarski(C_135,k1_relat_1(A_133))
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(A_11,B_12)
      | ~ r2_hidden(A_11,k1_relat_1(k7_relat_1(C_13,B_12)))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4316,plain,(
    ! [A_192,B_193,C_194,B_195] :
      ( r2_hidden('#skF_1'(A_192,B_193,k1_relat_1(k7_relat_1(C_194,B_195))),B_195)
      | ~ v1_relat_1(C_194)
      | k7_relat_1(B_193,k1_relat_1(k7_relat_1(C_194,B_195))) = k7_relat_1(A_192,k1_relat_1(k7_relat_1(C_194,B_195)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_194,B_195)),k1_relat_1(B_193))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_194,B_195)),k1_relat_1(A_192))
      | ~ v1_funct_1(B_193)
      | ~ v1_relat_1(B_193)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_1776,c_18])).

tff(c_38,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_2',D_54) = k1_funct_1('#skF_3',D_54)
      | ~ r2_hidden(D_54,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4426,plain,(
    ! [A_196,B_197,C_198] :
      ( k1_funct_1('#skF_2','#skF_1'(A_196,B_197,k1_relat_1(k7_relat_1(C_198,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_196,B_197,k1_relat_1(k7_relat_1(C_198,'#skF_4'))))
      | ~ v1_relat_1(C_198)
      | k7_relat_1(B_197,k1_relat_1(k7_relat_1(C_198,'#skF_4'))) = k7_relat_1(A_196,k1_relat_1(k7_relat_1(C_198,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_198,'#skF_4')),k1_relat_1(B_197))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_198,'#skF_4')),k1_relat_1(A_196))
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197)
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(resolution,[status(thm)],[c_4316,c_38])).

tff(c_5764,plain,(
    ! [A_226,B_227] :
      ( k1_funct_1('#skF_2','#skF_1'(A_226,B_227,k1_relat_1(k7_relat_1(B_227,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_226,B_227,k1_relat_1(k7_relat_1(B_227,'#skF_4'))))
      | k7_relat_1(B_227,k1_relat_1(k7_relat_1(B_227,'#skF_4'))) = k7_relat_1(A_226,k1_relat_1(k7_relat_1(B_227,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_227,'#skF_4')),k1_relat_1(A_226))
      | ~ v1_funct_1(B_227)
      | ~ v1_funct_1(A_226)
      | ~ v1_relat_1(A_226)
      | ~ v1_relat_1(B_227) ) ),
    inference(resolution,[status(thm)],[c_20,c_4426])).

tff(c_5789,plain,(
    ! [B_227] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_227,k1_relat_1(k7_relat_1(B_227,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_227,k1_relat_1(k7_relat_1(B_227,'#skF_4'))))
      | k7_relat_1(B_227,k1_relat_1(k7_relat_1(B_227,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_227,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_227,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_227)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5764])).

tff(c_6330,plain,(
    ! [B_234] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_234,k1_relat_1(k7_relat_1(B_234,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_234,k1_relat_1(k7_relat_1(B_234,'#skF_4'))))
      | k7_relat_1(B_234,k1_relat_1(k7_relat_1(B_234,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_234,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_234,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_5789])).

tff(c_6342,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_6330])).

tff(c_6353,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4891,c_1676,c_6342])).

tff(c_6354,plain,(
    k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_6353])).

tff(c_32,plain,(
    ! [B_33,A_21,C_39] :
      ( k1_funct_1(B_33,'#skF_1'(A_21,B_33,C_39)) != k1_funct_1(A_21,'#skF_1'(A_21,B_33,C_39))
      | k7_relat_1(B_33,C_39) = k7_relat_1(A_21,C_39)
      | ~ r1_tarski(C_39,k1_relat_1(B_33))
      | ~ r1_tarski(C_39,k1_relat_1(A_21))
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6640,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6354,c_32])).

tff(c_6645,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_405,c_40,c_405,c_4891,c_1676,c_6640])).

tff(c_6647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_6645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.05/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.41  
% 7.05/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.41  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 7.05/2.41  
% 7.05/2.41  %Foreground sorts:
% 7.05/2.41  
% 7.05/2.41  
% 7.05/2.41  %Background operators:
% 7.05/2.41  
% 7.05/2.41  
% 7.05/2.41  %Foreground operators:
% 7.05/2.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.05/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.05/2.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.05/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.05/2.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.05/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.05/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.05/2.41  tff('#skF_2', type, '#skF_2': $i).
% 7.05/2.41  tff('#skF_3', type, '#skF_3': $i).
% 7.05/2.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.05/2.41  tff('#skF_4', type, '#skF_4': $i).
% 7.05/2.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.05/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.05/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.05/2.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.05/2.41  
% 7.05/2.43  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 7.05/2.43  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 7.05/2.43  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 7.05/2.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.05/2.43  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.05/2.43  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.05/2.43  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 7.05/2.43  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 7.05/2.43  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 7.05/2.43  tff(c_36, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.05/2.43  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.05/2.43  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.05/2.43  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.05/2.43  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.05/2.43  tff(c_40, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.05/2.43  tff(c_136, plain, (![B_68, A_69]: (k3_xboole_0(k1_relat_1(B_68), A_69)=k1_relat_1(k7_relat_1(B_68, A_69)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.05/2.43  tff(c_162, plain, (![A_69]: (k3_xboole_0(k1_relat_1('#skF_3'), A_69)=k1_relat_1(k7_relat_1('#skF_2', A_69)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_136])).
% 7.05/2.43  tff(c_171, plain, (![A_73]: (k3_xboole_0(k1_relat_1('#skF_3'), A_73)=k1_relat_1(k7_relat_1('#skF_2', A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_162])).
% 7.05/2.43  tff(c_22, plain, (![B_17, A_16]: (k3_xboole_0(k1_relat_1(B_17), A_16)=k1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.05/2.43  tff(c_177, plain, (![A_73]: (k1_relat_1(k7_relat_1('#skF_2', A_73))=k1_relat_1(k7_relat_1('#skF_3', A_73)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_22])).
% 7.05/2.43  tff(c_201, plain, (![A_73]: (k1_relat_1(k7_relat_1('#skF_2', A_73))=k1_relat_1(k7_relat_1('#skF_3', A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_177])).
% 7.05/2.43  tff(c_125, plain, (![B_66, A_67]: (r1_tarski(k1_relat_1(k7_relat_1(B_66, A_67)), k1_relat_1(B_66)) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.05/2.43  tff(c_131, plain, (![A_67]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_67)), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_125])).
% 7.05/2.43  tff(c_135, plain, (![A_67]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_67)), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_131])).
% 7.05/2.43  tff(c_405, plain, (![A_67]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_67)), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_135])).
% 7.05/2.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.05/2.43  tff(c_198, plain, (![A_1]: (k3_xboole_0(A_1, k1_relat_1('#skF_3'))=k1_relat_1(k7_relat_1('#skF_2', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_171])).
% 7.05/2.43  tff(c_403, plain, (![A_1]: (k3_xboole_0(A_1, k1_relat_1('#skF_3'))=k1_relat_1(k7_relat_1('#skF_3', A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_198])).
% 7.05/2.43  tff(c_26, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.19/2.43  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.19/2.43  tff(c_159, plain, (![A_10, A_69]: (k1_relat_1(k7_relat_1(k6_relat_1(A_10), A_69))=k3_xboole_0(A_10, A_69) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_136])).
% 7.19/2.43  tff(c_166, plain, (![A_10, A_69]: (k1_relat_1(k7_relat_1(k6_relat_1(A_10), A_69))=k3_xboole_0(A_10, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_159])).
% 7.19/2.43  tff(c_1250, plain, (![A_123, B_124]: (k7_relat_1(A_123, k1_relat_1(k7_relat_1(B_124, k1_relat_1(A_123))))=k7_relat_1(A_123, k1_relat_1(B_124)) | ~v1_relat_1(B_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.19/2.43  tff(c_1321, plain, (![A_123, A_10]: (k7_relat_1(A_123, k3_xboole_0(A_10, k1_relat_1(A_123)))=k7_relat_1(A_123, k1_relat_1(k6_relat_1(A_10))) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_166, c_1250])).
% 7.19/2.43  tff(c_4693, plain, (![A_204, A_205]: (k7_relat_1(A_204, k3_xboole_0(A_205, k1_relat_1(A_204)))=k7_relat_1(A_204, A_205) | ~v1_relat_1(A_204))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10, c_1321])).
% 7.19/2.43  tff(c_4827, plain, (![A_1]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_1)))=k7_relat_1('#skF_3', A_1) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_4693])).
% 7.19/2.43  tff(c_4891, plain, (![A_1]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_1)))=k7_relat_1('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4827])).
% 7.19/2.43  tff(c_1327, plain, (![B_124]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_124, k1_relat_1('#skF_3'))))=k7_relat_1('#skF_2', k1_relat_1(B_124)) | ~v1_relat_1(B_124) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1250])).
% 7.19/2.43  tff(c_1622, plain, (![B_129]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_129, k1_relat_1('#skF_3'))))=k7_relat_1('#skF_2', k1_relat_1(B_129)) | ~v1_relat_1(B_129))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1327])).
% 7.19/2.43  tff(c_1657, plain, (![A_10]: (k7_relat_1('#skF_2', k3_xboole_0(A_10, k1_relat_1('#skF_3')))=k7_relat_1('#skF_2', k1_relat_1(k6_relat_1(A_10))) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_1622])).
% 7.19/2.43  tff(c_1676, plain, (![A_10]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', A_10)))=k7_relat_1('#skF_2', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_403, c_10, c_1657])).
% 7.19/2.43  tff(c_20, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.19/2.43  tff(c_1776, plain, (![A_133, B_134, C_135]: (r2_hidden('#skF_1'(A_133, B_134, C_135), C_135) | k7_relat_1(B_134, C_135)=k7_relat_1(A_133, C_135) | ~r1_tarski(C_135, k1_relat_1(B_134)) | ~r1_tarski(C_135, k1_relat_1(A_133)) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.19/2.43  tff(c_18, plain, (![A_11, B_12, C_13]: (r2_hidden(A_11, B_12) | ~r2_hidden(A_11, k1_relat_1(k7_relat_1(C_13, B_12))) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.19/2.43  tff(c_4316, plain, (![A_192, B_193, C_194, B_195]: (r2_hidden('#skF_1'(A_192, B_193, k1_relat_1(k7_relat_1(C_194, B_195))), B_195) | ~v1_relat_1(C_194) | k7_relat_1(B_193, k1_relat_1(k7_relat_1(C_194, B_195)))=k7_relat_1(A_192, k1_relat_1(k7_relat_1(C_194, B_195))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_194, B_195)), k1_relat_1(B_193)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_194, B_195)), k1_relat_1(A_192)) | ~v1_funct_1(B_193) | ~v1_relat_1(B_193) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_1776, c_18])).
% 7.19/2.43  tff(c_38, plain, (![D_54]: (k1_funct_1('#skF_2', D_54)=k1_funct_1('#skF_3', D_54) | ~r2_hidden(D_54, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.19/2.43  tff(c_4426, plain, (![A_196, B_197, C_198]: (k1_funct_1('#skF_2', '#skF_1'(A_196, B_197, k1_relat_1(k7_relat_1(C_198, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_196, B_197, k1_relat_1(k7_relat_1(C_198, '#skF_4')))) | ~v1_relat_1(C_198) | k7_relat_1(B_197, k1_relat_1(k7_relat_1(C_198, '#skF_4')))=k7_relat_1(A_196, k1_relat_1(k7_relat_1(C_198, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_198, '#skF_4')), k1_relat_1(B_197)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_198, '#skF_4')), k1_relat_1(A_196)) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197) | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(resolution, [status(thm)], [c_4316, c_38])).
% 7.19/2.43  tff(c_5764, plain, (![A_226, B_227]: (k1_funct_1('#skF_2', '#skF_1'(A_226, B_227, k1_relat_1(k7_relat_1(B_227, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_226, B_227, k1_relat_1(k7_relat_1(B_227, '#skF_4')))) | k7_relat_1(B_227, k1_relat_1(k7_relat_1(B_227, '#skF_4')))=k7_relat_1(A_226, k1_relat_1(k7_relat_1(B_227, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_227, '#skF_4')), k1_relat_1(A_226)) | ~v1_funct_1(B_227) | ~v1_funct_1(A_226) | ~v1_relat_1(A_226) | ~v1_relat_1(B_227))), inference(resolution, [status(thm)], [c_20, c_4426])).
% 7.19/2.43  tff(c_5789, plain, (![B_227]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_227, k1_relat_1(k7_relat_1(B_227, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_227, k1_relat_1(k7_relat_1(B_227, '#skF_4')))) | k7_relat_1(B_227, k1_relat_1(k7_relat_1(B_227, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_227, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_227, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_227) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_227))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5764])).
% 7.19/2.43  tff(c_6330, plain, (![B_234]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_234, k1_relat_1(k7_relat_1(B_234, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_234, k1_relat_1(k7_relat_1(B_234, '#skF_4')))) | k7_relat_1(B_234, k1_relat_1(k7_relat_1(B_234, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_234, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_234, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_234) | ~v1_relat_1(B_234))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_5789])).
% 7.19/2.43  tff(c_6342, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_6330])).
% 7.19/2.43  tff(c_6353, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4891, c_1676, c_6342])).
% 7.19/2.43  tff(c_6354, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_6353])).
% 7.19/2.43  tff(c_32, plain, (![B_33, A_21, C_39]: (k1_funct_1(B_33, '#skF_1'(A_21, B_33, C_39))!=k1_funct_1(A_21, '#skF_1'(A_21, B_33, C_39)) | k7_relat_1(B_33, C_39)=k7_relat_1(A_21, C_39) | ~r1_tarski(C_39, k1_relat_1(B_33)) | ~r1_tarski(C_39, k1_relat_1(A_21)) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.19/2.43  tff(c_6640, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6354, c_32])).
% 7.19/2.43  tff(c_6645, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_405, c_40, c_405, c_4891, c_1676, c_6640])).
% 7.19/2.43  tff(c_6647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_6645])).
% 7.19/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.43  
% 7.19/2.43  Inference rules
% 7.19/2.43  ----------------------
% 7.19/2.43  #Ref     : 2
% 7.19/2.43  #Sup     : 1580
% 7.19/2.43  #Fact    : 0
% 7.19/2.43  #Define  : 0
% 7.19/2.43  #Split   : 2
% 7.19/2.43  #Chain   : 0
% 7.19/2.43  #Close   : 0
% 7.19/2.43  
% 7.19/2.43  Ordering : KBO
% 7.19/2.43  
% 7.19/2.43  Simplification rules
% 7.19/2.43  ----------------------
% 7.19/2.43  #Subsume      : 200
% 7.19/2.43  #Demod        : 2546
% 7.19/2.43  #Tautology    : 709
% 7.19/2.43  #SimpNegUnit  : 3
% 7.19/2.43  #BackRed      : 7
% 7.19/2.43  
% 7.19/2.43  #Partial instantiations: 0
% 7.19/2.43  #Strategies tried      : 1
% 7.19/2.43  
% 7.19/2.43  Timing (in seconds)
% 7.19/2.43  ----------------------
% 7.19/2.43  Preprocessing        : 0.32
% 7.19/2.43  Parsing              : 0.17
% 7.19/2.43  CNF conversion       : 0.02
% 7.19/2.43  Main loop            : 1.35
% 7.19/2.43  Inferencing          : 0.36
% 7.19/2.43  Reduction            : 0.63
% 7.19/2.43  Demodulation         : 0.53
% 7.19/2.43  BG Simplification    : 0.06
% 7.19/2.43  Subsumption          : 0.22
% 7.19/2.43  Abstraction          : 0.08
% 7.19/2.43  MUC search           : 0.00
% 7.19/2.43  Cooper               : 0.00
% 7.19/2.43  Total                : 1.70
% 7.19/2.43  Index Insertion      : 0.00
% 7.19/2.43  Index Deletion       : 0.00
% 7.19/2.43  Index Matching       : 0.00
% 7.19/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
