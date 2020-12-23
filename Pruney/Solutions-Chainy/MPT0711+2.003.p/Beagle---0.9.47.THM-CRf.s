%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:29 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 301 expanded)
%              Number of leaves         :   28 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  159 ( 868 expanded)
%              Number of equality atoms :   53 ( 349 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_93,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_36,plain,(
    k7_relat_1('#skF_3','#skF_5') != k7_relat_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k3_xboole_0(k1_relat_1(B_16),A_15) = k1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_136,plain,(
    ! [B_73,A_74] :
      ( k3_xboole_0(k1_relat_1(B_73),A_74) = k1_relat_1(k7_relat_1(B_73,A_74))
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_159,plain,(
    ! [A_74] :
      ( k3_xboole_0(k1_relat_1('#skF_4'),A_74) = k1_relat_1(k7_relat_1('#skF_3',A_74))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_136])).

tff(c_192,plain,(
    ! [A_80] : k3_xboole_0(k1_relat_1('#skF_4'),A_80) = k1_relat_1(k7_relat_1('#skF_3',A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_159])).

tff(c_211,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_15)) = k1_relat_1(k7_relat_1('#skF_4',A_15))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_192])).

tff(c_225,plain,(
    ! [A_15] : k1_relat_1(k7_relat_1('#skF_3',A_15)) = k1_relat_1(k7_relat_1('#skF_4',A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_211])).

tff(c_125,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_71,A_72)),k1_relat_1(B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_128,plain,(
    ! [A_72] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_72)),k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_125])).

tff(c_133,plain,(
    ! [A_72] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_72)),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_128])).

tff(c_320,plain,(
    ! [A_72] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_72)),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_133])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_215,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_relat_1('#skF_4')) = k1_relat_1(k7_relat_1('#skF_3',B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_395,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_relat_1('#skF_4')) = k1_relat_1(k7_relat_1('#skF_4',B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_215])).

tff(c_28,plain,(
    ! [A_19] : v1_relat_1('#skF_1'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_19] : k1_relat_1('#skF_1'(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_162,plain,(
    ! [A_19,A_74] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_19),A_74)) = k3_xboole_0(A_19,A_74)
      | ~ v1_relat_1('#skF_1'(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_136])).

tff(c_168,plain,(
    ! [A_19,A_74] : k1_relat_1(k7_relat_1('#skF_1'(A_19),A_74)) = k3_xboole_0(A_19,A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_162])).

tff(c_893,plain,(
    ! [A_119,B_120] :
      ( k7_relat_1(A_119,k1_relat_1(k7_relat_1(B_120,k1_relat_1(A_119)))) = k7_relat_1(A_119,k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_961,plain,(
    ! [A_119,A_19] :
      ( k7_relat_1(A_119,k3_xboole_0(A_19,k1_relat_1(A_119))) = k7_relat_1(A_119,k1_relat_1('#skF_1'(A_19)))
      | ~ v1_relat_1('#skF_1'(A_19))
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_893])).

tff(c_5253,plain,(
    ! [A_220,A_221] :
      ( k7_relat_1(A_220,k3_xboole_0(A_221,k1_relat_1(A_220))) = k7_relat_1(A_220,A_221)
      | ~ v1_relat_1(A_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_961])).

tff(c_5395,plain,(
    ! [B_2] :
      ( k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4',B_2))) = k7_relat_1('#skF_4',B_2)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_5253])).

tff(c_5460,plain,(
    ! [B_2] : k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4',B_2))) = k7_relat_1('#skF_4',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5395])).

tff(c_964,plain,(
    ! [B_120] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_120,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_893])).

tff(c_1108,plain,(
    ! [B_123] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_123,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_123))
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_964])).

tff(c_1140,plain,(
    ! [A_19] :
      ( k7_relat_1('#skF_3',k3_xboole_0(A_19,k1_relat_1('#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1('#skF_1'(A_19)))
      | ~ v1_relat_1('#skF_1'(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_1108])).

tff(c_1157,plain,(
    ! [A_19] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4',A_19))) = k7_relat_1('#skF_3',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_395,c_24,c_1140])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2017,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_2'(A_140,B_141,C_142),C_142)
      | k7_relat_1(B_141,C_142) = k7_relat_1(A_140,C_142)
      | ~ r1_tarski(C_142,k1_relat_1(B_141))
      | ~ r1_tarski(C_142,k1_relat_1(A_140))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden(A_10,B_11)
      | ~ r2_hidden(A_10,k1_relat_1(k7_relat_1(C_12,B_11)))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4933,plain,(
    ! [A_208,B_209,C_210,B_211] :
      ( r2_hidden('#skF_2'(A_208,B_209,k1_relat_1(k7_relat_1(C_210,B_211))),B_211)
      | ~ v1_relat_1(C_210)
      | k7_relat_1(B_209,k1_relat_1(k7_relat_1(C_210,B_211))) = k7_relat_1(A_208,k1_relat_1(k7_relat_1(C_210,B_211)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_210,B_211)),k1_relat_1(B_209))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_210,B_211)),k1_relat_1(A_208))
      | ~ v1_funct_1(B_209)
      | ~ v1_relat_1(B_209)
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_2017,c_14])).

tff(c_38,plain,(
    ! [D_58] :
      ( k1_funct_1('#skF_3',D_58) = k1_funct_1('#skF_4',D_58)
      | ~ r2_hidden(D_58,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5046,plain,(
    ! [A_212,B_213,C_214] :
      ( k1_funct_1('#skF_3','#skF_2'(A_212,B_213,k1_relat_1(k7_relat_1(C_214,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'(A_212,B_213,k1_relat_1(k7_relat_1(C_214,'#skF_5'))))
      | ~ v1_relat_1(C_214)
      | k7_relat_1(B_213,k1_relat_1(k7_relat_1(C_214,'#skF_5'))) = k7_relat_1(A_212,k1_relat_1(k7_relat_1(C_214,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_214,'#skF_5')),k1_relat_1(B_213))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_214,'#skF_5')),k1_relat_1(A_212))
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_4933,c_38])).

tff(c_6349,plain,(
    ! [A_242,B_243] :
      ( k1_funct_1('#skF_3','#skF_2'(A_242,B_243,k1_relat_1(k7_relat_1(B_243,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'(A_242,B_243,k1_relat_1(k7_relat_1(B_243,'#skF_5'))))
      | k7_relat_1(B_243,k1_relat_1(k7_relat_1(B_243,'#skF_5'))) = k7_relat_1(A_242,k1_relat_1(k7_relat_1(B_243,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_243,'#skF_5')),k1_relat_1(A_242))
      | ~ v1_funct_1(B_243)
      | ~ v1_funct_1(A_242)
      | ~ v1_relat_1(A_242)
      | ~ v1_relat_1(B_243) ) ),
    inference(resolution,[status(thm)],[c_16,c_5046])).

tff(c_6372,plain,(
    ! [B_243] :
      ( k1_funct_1('#skF_3','#skF_2'('#skF_3',B_243,k1_relat_1(k7_relat_1(B_243,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3',B_243,k1_relat_1(k7_relat_1(B_243,'#skF_5'))))
      | k7_relat_1(B_243,k1_relat_1(k7_relat_1(B_243,'#skF_5'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_243,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_243,'#skF_5')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_243)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6349])).

tff(c_7216,plain,(
    ! [B_254] :
      ( k1_funct_1('#skF_3','#skF_2'('#skF_3',B_254,k1_relat_1(k7_relat_1(B_254,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3',B_254,k1_relat_1(k7_relat_1(B_254,'#skF_5'))))
      | k7_relat_1(B_254,k1_relat_1(k7_relat_1(B_254,'#skF_5'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_254,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_254,'#skF_5')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_254)
      | ~ v1_relat_1(B_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6372])).

tff(c_7228,plain,
    ( k1_funct_1('#skF_3','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))))
    | k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_7216])).

tff(c_7239,plain,
    ( k1_funct_1('#skF_3','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))))
    | k7_relat_1('#skF_3','#skF_5') = k7_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5460,c_1157,c_7228])).

tff(c_7240,plain,(
    k1_funct_1('#skF_3','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_7239])).

tff(c_32,plain,(
    ! [B_37,A_25,C_43] :
      ( k1_funct_1(B_37,'#skF_2'(A_25,B_37,C_43)) != k1_funct_1(A_25,'#skF_2'(A_25,B_37,C_43))
      | k7_relat_1(B_37,C_43) = k7_relat_1(A_25,C_43)
      | ~ r1_tarski(C_43,k1_relat_1(B_37))
      | ~ r1_tarski(C_43,k1_relat_1(A_25))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_7246,plain,
    ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7240,c_32])).

tff(c_7251,plain,(
    k7_relat_1('#skF_3','#skF_5') = k7_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_320,c_40,c_320,c_5460,c_1157,c_7246])).

tff(c_7253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_7251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.90  
% 7.65/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.90  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 7.65/2.90  
% 7.65/2.90  %Foreground sorts:
% 7.65/2.90  
% 7.65/2.90  
% 7.65/2.90  %Background operators:
% 7.65/2.90  
% 7.65/2.90  
% 7.65/2.90  %Foreground operators:
% 7.65/2.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.65/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.65/2.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.65/2.90  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.65/2.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.65/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.65/2.90  tff('#skF_5', type, '#skF_5': $i).
% 7.65/2.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.65/2.90  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.65/2.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.65/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.65/2.90  tff('#skF_4', type, '#skF_4': $i).
% 7.65/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.65/2.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.65/2.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.65/2.90  
% 7.65/2.92  tff(f_113, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 7.65/2.92  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 7.65/2.92  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 7.65/2.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.65/2.92  tff(f_72, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 7.65/2.92  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 7.65/2.92  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 7.65/2.92  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 7.65/2.92  tff(c_36, plain, (k7_relat_1('#skF_3', '#skF_5')!=k7_relat_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.65/2.92  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.65/2.92  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.65/2.92  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.65/2.92  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.65/2.92  tff(c_18, plain, (![B_16, A_15]: (k3_xboole_0(k1_relat_1(B_16), A_15)=k1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.65/2.92  tff(c_40, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.65/2.92  tff(c_136, plain, (![B_73, A_74]: (k3_xboole_0(k1_relat_1(B_73), A_74)=k1_relat_1(k7_relat_1(B_73, A_74)) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.65/2.92  tff(c_159, plain, (![A_74]: (k3_xboole_0(k1_relat_1('#skF_4'), A_74)=k1_relat_1(k7_relat_1('#skF_3', A_74)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_136])).
% 7.65/2.92  tff(c_192, plain, (![A_80]: (k3_xboole_0(k1_relat_1('#skF_4'), A_80)=k1_relat_1(k7_relat_1('#skF_3', A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_159])).
% 7.65/2.92  tff(c_211, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_3', A_15))=k1_relat_1(k7_relat_1('#skF_4', A_15)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_192])).
% 7.65/2.92  tff(c_225, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_3', A_15))=k1_relat_1(k7_relat_1('#skF_4', A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_211])).
% 7.65/2.92  tff(c_125, plain, (![B_71, A_72]: (r1_tarski(k1_relat_1(k7_relat_1(B_71, A_72)), k1_relat_1(B_71)) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.65/2.92  tff(c_128, plain, (![A_72]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_72)), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_125])).
% 7.65/2.92  tff(c_133, plain, (![A_72]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_72)), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_128])).
% 7.65/2.92  tff(c_320, plain, (![A_72]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_72)), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_133])).
% 7.65/2.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.65/2.92  tff(c_215, plain, (![B_2]: (k3_xboole_0(B_2, k1_relat_1('#skF_4'))=k1_relat_1(k7_relat_1('#skF_3', B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_192])).
% 7.65/2.92  tff(c_395, plain, (![B_2]: (k3_xboole_0(B_2, k1_relat_1('#skF_4'))=k1_relat_1(k7_relat_1('#skF_4', B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_215])).
% 7.65/2.92  tff(c_28, plain, (![A_19]: (v1_relat_1('#skF_1'(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.65/2.92  tff(c_24, plain, (![A_19]: (k1_relat_1('#skF_1'(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.65/2.92  tff(c_162, plain, (![A_19, A_74]: (k1_relat_1(k7_relat_1('#skF_1'(A_19), A_74))=k3_xboole_0(A_19, A_74) | ~v1_relat_1('#skF_1'(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_136])).
% 7.65/2.92  tff(c_168, plain, (![A_19, A_74]: (k1_relat_1(k7_relat_1('#skF_1'(A_19), A_74))=k3_xboole_0(A_19, A_74))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_162])).
% 7.65/2.92  tff(c_893, plain, (![A_119, B_120]: (k7_relat_1(A_119, k1_relat_1(k7_relat_1(B_120, k1_relat_1(A_119))))=k7_relat_1(A_119, k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.65/2.92  tff(c_961, plain, (![A_119, A_19]: (k7_relat_1(A_119, k3_xboole_0(A_19, k1_relat_1(A_119)))=k7_relat_1(A_119, k1_relat_1('#skF_1'(A_19))) | ~v1_relat_1('#skF_1'(A_19)) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_168, c_893])).
% 7.65/2.92  tff(c_5253, plain, (![A_220, A_221]: (k7_relat_1(A_220, k3_xboole_0(A_221, k1_relat_1(A_220)))=k7_relat_1(A_220, A_221) | ~v1_relat_1(A_220))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_961])).
% 7.65/2.92  tff(c_5395, plain, (![B_2]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', B_2)))=k7_relat_1('#skF_4', B_2) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_395, c_5253])).
% 7.65/2.92  tff(c_5460, plain, (![B_2]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', B_2)))=k7_relat_1('#skF_4', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5395])).
% 7.65/2.92  tff(c_964, plain, (![B_120]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_120, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_893])).
% 7.65/2.92  tff(c_1108, plain, (![B_123]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_123, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_123)) | ~v1_relat_1(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_964])).
% 7.65/2.92  tff(c_1140, plain, (![A_19]: (k7_relat_1('#skF_3', k3_xboole_0(A_19, k1_relat_1('#skF_4')))=k7_relat_1('#skF_3', k1_relat_1('#skF_1'(A_19))) | ~v1_relat_1('#skF_1'(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_1108])).
% 7.65/2.92  tff(c_1157, plain, (![A_19]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', A_19)))=k7_relat_1('#skF_3', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_395, c_24, c_1140])).
% 7.65/2.92  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.65/2.92  tff(c_2017, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_2'(A_140, B_141, C_142), C_142) | k7_relat_1(B_141, C_142)=k7_relat_1(A_140, C_142) | ~r1_tarski(C_142, k1_relat_1(B_141)) | ~r1_tarski(C_142, k1_relat_1(A_140)) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.65/2.92  tff(c_14, plain, (![A_10, B_11, C_12]: (r2_hidden(A_10, B_11) | ~r2_hidden(A_10, k1_relat_1(k7_relat_1(C_12, B_11))) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.65/2.92  tff(c_4933, plain, (![A_208, B_209, C_210, B_211]: (r2_hidden('#skF_2'(A_208, B_209, k1_relat_1(k7_relat_1(C_210, B_211))), B_211) | ~v1_relat_1(C_210) | k7_relat_1(B_209, k1_relat_1(k7_relat_1(C_210, B_211)))=k7_relat_1(A_208, k1_relat_1(k7_relat_1(C_210, B_211))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_210, B_211)), k1_relat_1(B_209)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_210, B_211)), k1_relat_1(A_208)) | ~v1_funct_1(B_209) | ~v1_relat_1(B_209) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_2017, c_14])).
% 7.65/2.92  tff(c_38, plain, (![D_58]: (k1_funct_1('#skF_3', D_58)=k1_funct_1('#skF_4', D_58) | ~r2_hidden(D_58, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.65/2.92  tff(c_5046, plain, (![A_212, B_213, C_214]: (k1_funct_1('#skF_3', '#skF_2'(A_212, B_213, k1_relat_1(k7_relat_1(C_214, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'(A_212, B_213, k1_relat_1(k7_relat_1(C_214, '#skF_5')))) | ~v1_relat_1(C_214) | k7_relat_1(B_213, k1_relat_1(k7_relat_1(C_214, '#skF_5')))=k7_relat_1(A_212, k1_relat_1(k7_relat_1(C_214, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_214, '#skF_5')), k1_relat_1(B_213)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_214, '#skF_5')), k1_relat_1(A_212)) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(resolution, [status(thm)], [c_4933, c_38])).
% 7.65/2.92  tff(c_6349, plain, (![A_242, B_243]: (k1_funct_1('#skF_3', '#skF_2'(A_242, B_243, k1_relat_1(k7_relat_1(B_243, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'(A_242, B_243, k1_relat_1(k7_relat_1(B_243, '#skF_5')))) | k7_relat_1(B_243, k1_relat_1(k7_relat_1(B_243, '#skF_5')))=k7_relat_1(A_242, k1_relat_1(k7_relat_1(B_243, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_243, '#skF_5')), k1_relat_1(A_242)) | ~v1_funct_1(B_243) | ~v1_funct_1(A_242) | ~v1_relat_1(A_242) | ~v1_relat_1(B_243))), inference(resolution, [status(thm)], [c_16, c_5046])).
% 7.65/2.92  tff(c_6372, plain, (![B_243]: (k1_funct_1('#skF_3', '#skF_2'('#skF_3', B_243, k1_relat_1(k7_relat_1(B_243, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', B_243, k1_relat_1(k7_relat_1(B_243, '#skF_5')))) | k7_relat_1(B_243, k1_relat_1(k7_relat_1(B_243, '#skF_5')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_243, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_243, '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_243) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_243))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6349])).
% 7.65/2.92  tff(c_7216, plain, (![B_254]: (k1_funct_1('#skF_3', '#skF_2'('#skF_3', B_254, k1_relat_1(k7_relat_1(B_254, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', B_254, k1_relat_1(k7_relat_1(B_254, '#skF_5')))) | k7_relat_1(B_254, k1_relat_1(k7_relat_1(B_254, '#skF_5')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_254, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_254, '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_254) | ~v1_relat_1(B_254))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_6372])).
% 7.65/2.92  tff(c_7228, plain, (k1_funct_1('#skF_3', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))) | k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_7216])).
% 7.65/2.92  tff(c_7239, plain, (k1_funct_1('#skF_3', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))) | k7_relat_1('#skF_3', '#skF_5')=k7_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_5460, c_1157, c_7228])).
% 7.65/2.92  tff(c_7240, plain, (k1_funct_1('#skF_3', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_7239])).
% 7.65/2.92  tff(c_32, plain, (![B_37, A_25, C_43]: (k1_funct_1(B_37, '#skF_2'(A_25, B_37, C_43))!=k1_funct_1(A_25, '#skF_2'(A_25, B_37, C_43)) | k7_relat_1(B_37, C_43)=k7_relat_1(A_25, C_43) | ~r1_tarski(C_43, k1_relat_1(B_37)) | ~r1_tarski(C_43, k1_relat_1(A_25)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.65/2.92  tff(c_7246, plain, (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7240, c_32])).
% 7.65/2.92  tff(c_7251, plain, (k7_relat_1('#skF_3', '#skF_5')=k7_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_320, c_40, c_320, c_5460, c_1157, c_7246])).
% 7.65/2.92  tff(c_7253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_7251])).
% 7.65/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/2.92  
% 7.65/2.92  Inference rules
% 7.65/2.92  ----------------------
% 7.65/2.92  #Ref     : 2
% 7.65/2.92  #Sup     : 1727
% 7.65/2.92  #Fact    : 0
% 7.65/2.92  #Define  : 0
% 7.65/2.92  #Split   : 2
% 7.65/2.92  #Chain   : 0
% 7.65/2.92  #Close   : 0
% 7.65/2.92  
% 7.65/2.92  Ordering : KBO
% 7.65/2.92  
% 7.65/2.92  Simplification rules
% 7.65/2.92  ----------------------
% 7.65/2.92  #Subsume      : 255
% 7.65/2.92  #Demod        : 2765
% 7.65/2.92  #Tautology    : 778
% 7.65/2.92  #SimpNegUnit  : 3
% 7.65/2.92  #BackRed      : 5
% 7.65/2.92  
% 7.65/2.92  #Partial instantiations: 0
% 7.65/2.92  #Strategies tried      : 1
% 7.65/2.92  
% 7.65/2.92  Timing (in seconds)
% 7.65/2.92  ----------------------
% 7.65/2.92  Preprocessing        : 0.51
% 7.65/2.92  Parsing              : 0.26
% 7.65/2.92  CNF conversion       : 0.04
% 7.65/2.92  Main loop            : 1.54
% 7.65/2.92  Inferencing          : 0.40
% 7.65/2.92  Reduction            : 0.73
% 7.65/2.92  Demodulation         : 0.62
% 7.65/2.92  BG Simplification    : 0.09
% 7.65/2.92  Subsumption          : 0.24
% 7.65/2.92  Abstraction          : 0.09
% 7.65/2.92  MUC search           : 0.00
% 7.65/2.92  Cooper               : 0.00
% 7.65/2.92  Total                : 2.09
% 7.65/2.92  Index Insertion      : 0.00
% 7.65/2.92  Index Deletion       : 0.00
% 7.65/2.92  Index Matching       : 0.00
% 7.65/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
