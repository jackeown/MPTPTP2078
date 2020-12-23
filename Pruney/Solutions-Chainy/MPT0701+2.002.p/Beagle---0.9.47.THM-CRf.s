%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:02 EST 2020

% Result     : Theorem 11.33s
% Output     : CNFRefutation 11.33s
% Verified   : 
% Statistics : Number of formulae       :  118 (1002 expanded)
%              Number of leaves         :   29 ( 385 expanded)
%              Depth                    :   29
%              Number of atoms          :  298 (4732 expanded)
%              Number of equality atoms :   42 (1509 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ! [D] :
                ( ( v1_relat_1(D)
                  & v1_funct_1(D) )
               => ( ( A = k2_relat_1(B)
                    & k1_relat_1(C) = A
                    & k1_relat_1(D) = A
                    & k5_relat_1(B,C) = k5_relat_1(B,D) )
                 => C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_44,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ! [A_3,B_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),A_3)
      | r1_tarski(A_3,B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,(
    ! [C_102,D_103,B_104,A_105] :
      ( r2_hidden(k4_tarski(C_102,D_103),B_104)
      | ~ r2_hidden(k4_tarski(C_102,D_103),A_105)
      | ~ r1_tarski(A_105,B_104)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_263,plain,(
    ! [A_122,B_123,B_124] :
      ( r2_hidden(k4_tarski('#skF_1'(A_122,B_123),'#skF_2'(A_122,B_123)),B_124)
      | ~ r1_tarski(A_122,B_124)
      | r1_tarski(A_122,B_123)
      | ~ v1_relat_1(A_122) ) ),
    inference(resolution,[status(thm)],[c_12,c_154])).

tff(c_16,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(A_20,k1_relat_1(C_22))
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_315,plain,(
    ! [A_131,B_132,B_133] :
      ( r2_hidden('#skF_1'(A_131,B_132),k1_relat_1(B_133))
      | ~ v1_relat_1(B_133)
      | ~ r1_tarski(A_131,B_133)
      | r1_tarski(A_131,B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(resolution,[status(thm)],[c_263,c_16])).

tff(c_321,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_1'(A_131,B_132),'#skF_7')
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(A_131,'#skF_10')
      | r1_tarski(A_131,B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_315])).

tff(c_325,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_1'(A_131,B_132),'#skF_7')
      | ~ r1_tarski(A_131,'#skF_10')
      | r1_tarski(A_131,B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_321])).

tff(c_60,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_93,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(k4_tarski('#skF_1'(A_86,B_87),'#skF_2'(A_86,B_87)),A_86)
      | r1_tarski(A_86,B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95),k1_relat_1(A_94))
      | r1_tarski(A_94,B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_93,c_16])).

tff(c_126,plain,(
    ! [B_95] :
      ( r2_hidden('#skF_1'('#skF_10',B_95),'#skF_7')
      | r1_tarski('#skF_10',B_95)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_120])).

tff(c_130,plain,(
    ! [B_95] :
      ( r2_hidden('#skF_1'('#skF_10',B_95),'#skF_7')
      | r1_tarski('#skF_10',B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_126])).

tff(c_64,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_182,plain,(
    ! [A_108,C_109] :
      ( k1_funct_1(A_108,'#skF_6'(A_108,k2_relat_1(A_108),C_109)) = C_109
      | ~ r2_hidden(C_109,k2_relat_1(A_108))
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ! [C_109] :
      ( k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_109)) = C_109
      | ~ r2_hidden(C_109,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_182])).

tff(c_207,plain,(
    ! [C_109] :
      ( k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_109)) = C_109
      | ~ r2_hidden(C_109,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_201])).

tff(c_46,plain,(
    k5_relat_1('#skF_8','#skF_10') = k5_relat_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_230,plain,(
    ! [A_111,C_112] :
      ( r2_hidden('#skF_6'(A_111,k2_relat_1(A_111),C_112),k1_relat_1(A_111))
      | ~ r2_hidden(C_112,k2_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_239,plain,(
    ! [C_112] :
      ( r2_hidden('#skF_6'('#skF_8','#skF_7',C_112),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_112,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_230])).

tff(c_245,plain,(
    ! [C_112] :
      ( r2_hidden('#skF_6'('#skF_8','#skF_7',C_112),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_112,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_239])).

tff(c_530,plain,(
    ! [B_164,C_165,A_166] :
      ( k1_funct_1(k5_relat_1(B_164,C_165),A_166) = k1_funct_1(C_165,k1_funct_1(B_164,A_166))
      | ~ r2_hidden(A_166,k1_relat_1(B_164))
      | ~ v1_funct_1(C_165)
      | ~ v1_relat_1(C_165)
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_554,plain,(
    ! [C_165,C_112] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_165),'#skF_6'('#skF_8','#skF_7',C_112)) = k1_funct_1(C_165,k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_112)))
      | ~ v1_funct_1(C_165)
      | ~ v1_relat_1(C_165)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_112,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_245,c_530])).

tff(c_1012,plain,(
    ! [C_223,C_224] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_223),'#skF_6'('#skF_8','#skF_7',C_224)) = k1_funct_1(C_223,k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_224)))
      | ~ v1_funct_1(C_223)
      | ~ v1_relat_1(C_223)
      | ~ r2_hidden(C_224,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_554])).

tff(c_1040,plain,(
    ! [C_224] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_9'),'#skF_6'('#skF_8','#skF_7',C_224)) = k1_funct_1('#skF_10',k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_224)))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_224,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1012])).

tff(c_1110,plain,(
    ! [C_229] :
      ( k1_funct_1(k5_relat_1('#skF_8','#skF_9'),'#skF_6'('#skF_8','#skF_7',C_229)) = k1_funct_1('#skF_10',k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_229)))
      | ~ r2_hidden(C_229,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1040])).

tff(c_579,plain,(
    ! [C_165,C_112] :
      ( k1_funct_1(k5_relat_1('#skF_8',C_165),'#skF_6'('#skF_8','#skF_7',C_112)) = k1_funct_1(C_165,k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_112)))
      | ~ v1_funct_1(C_165)
      | ~ v1_relat_1(C_165)
      | ~ r2_hidden(C_112,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_554])).

tff(c_1116,plain,(
    ! [C_229] :
      ( k1_funct_1('#skF_10',k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_229))) = k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_229)))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_229,'#skF_7')
      | ~ r2_hidden(C_229,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_579])).

tff(c_1149,plain,(
    ! [C_230] :
      ( k1_funct_1('#skF_10',k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_230))) = k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_230)))
      | ~ r2_hidden(C_230,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1116])).

tff(c_1194,plain,(
    ! [C_231] :
      ( k1_funct_1('#skF_9',k1_funct_1('#skF_8','#skF_6'('#skF_8','#skF_7',C_231))) = k1_funct_1('#skF_10',C_231)
      | ~ r2_hidden(C_231,'#skF_7')
      | ~ r2_hidden(C_231,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1149])).

tff(c_1239,plain,(
    ! [C_232] :
      ( k1_funct_1('#skF_10',C_232) = k1_funct_1('#skF_9',C_232)
      | ~ r2_hidden(C_232,'#skF_7')
      | ~ r2_hidden(C_232,'#skF_7')
      | ~ r2_hidden(C_232,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1194])).

tff(c_2246,plain,(
    ! [B_267] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_10',B_267)) = k1_funct_1('#skF_9','#skF_1'('#skF_10',B_267))
      | ~ r2_hidden('#skF_1'('#skF_10',B_267),'#skF_7')
      | r1_tarski('#skF_10',B_267) ) ),
    inference(resolution,[status(thm)],[c_130,c_1239])).

tff(c_2250,plain,(
    ! [B_132] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_10',B_132)) = k1_funct_1('#skF_9','#skF_1'('#skF_10',B_132))
      | ~ r1_tarski('#skF_10','#skF_10')
      | r1_tarski('#skF_10',B_132)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_325,c_2246])).

tff(c_2265,plain,(
    ! [B_268] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_10',B_268)) = k1_funct_1('#skF_9','#skF_1'('#skF_10',B_268))
      | r1_tarski('#skF_10',B_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6,c_2250])).

tff(c_40,plain,(
    ! [C_69,A_67,B_68] :
      ( k1_funct_1(C_69,A_67) = B_68
      | ~ r2_hidden(k4_tarski(A_67,B_68),C_69)
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_281,plain,(
    ! [B_124,A_122,B_123] :
      ( k1_funct_1(B_124,'#skF_1'(A_122,B_123)) = '#skF_2'(A_122,B_123)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ r1_tarski(A_122,B_124)
      | r1_tarski(A_122,B_123)
      | ~ v1_relat_1(A_122) ) ),
    inference(resolution,[status(thm)],[c_263,c_40])).

tff(c_2278,plain,(
    ! [B_268] :
      ( k1_funct_1('#skF_9','#skF_1'('#skF_10',B_268)) = '#skF_2'('#skF_10',B_268)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski('#skF_10','#skF_10')
      | r1_tarski('#skF_10',B_268)
      | ~ v1_relat_1('#skF_10')
      | r1_tarski('#skF_10',B_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2265,c_281])).

tff(c_2332,plain,(
    ! [B_269] :
      ( k1_funct_1('#skF_9','#skF_1'('#skF_10',B_269)) = '#skF_2'('#skF_10',B_269)
      | r1_tarski('#skF_10',B_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6,c_56,c_54,c_2278])).

tff(c_38,plain,(
    ! [A_67,C_69] :
      ( r2_hidden(k4_tarski(A_67,k1_funct_1(C_69,A_67)),C_69)
      | ~ r2_hidden(A_67,k1_relat_1(C_69))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2357,plain,(
    ! [B_269] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_10',B_269),'#skF_2'('#skF_10',B_269)),'#skF_9')
      | ~ r2_hidden('#skF_1'('#skF_10',B_269),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | r1_tarski('#skF_10',B_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2332,c_38])).

tff(c_2630,plain,(
    ! [B_284] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_10',B_284),'#skF_2'('#skF_10',B_284)),'#skF_9')
      | ~ r2_hidden('#skF_1'('#skF_10',B_284),'#skF_7')
      | r1_tarski('#skF_10',B_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_2357])).

tff(c_10,plain,(
    ! [A_3,B_13] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_3,B_13),'#skF_2'(A_3,B_13)),B_13)
      | r1_tarski(A_3,B_13)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2636,plain,
    ( ~ v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),'#skF_7')
    | r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_2630,c_10])).

tff(c_2651,plain,
    ( ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),'#skF_7')
    | r1_tarski('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2636])).

tff(c_2680,plain,(
    ~ r2_hidden('#skF_1'('#skF_10','#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2651])).

tff(c_2683,plain,
    ( ~ r1_tarski('#skF_10','#skF_10')
    | r1_tarski('#skF_10','#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_325,c_2680])).

tff(c_2692,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6,c_2683])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2706,plain,
    ( '#skF_10' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_2692,c_2])).

tff(c_2721,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2706])).

tff(c_318,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_1'(A_131,B_132),'#skF_7')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_131,'#skF_9')
      | r1_tarski(A_131,B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_315])).

tff(c_323,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_1'(A_131,B_132),'#skF_7')
      | ~ r1_tarski(A_131,'#skF_9')
      | r1_tarski(A_131,B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_318])).

tff(c_123,plain,(
    ! [B_95] :
      ( r2_hidden('#skF_1'('#skF_9',B_95),'#skF_7')
      | r1_tarski('#skF_9',B_95)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_128,plain,(
    ! [B_95] :
      ( r2_hidden('#skF_1'('#skF_9',B_95),'#skF_7')
      | r1_tarski('#skF_9',B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_123])).

tff(c_2661,plain,(
    ! [B_285] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_9',B_285)) = k1_funct_1('#skF_9','#skF_1'('#skF_9',B_285))
      | ~ r2_hidden('#skF_1'('#skF_9',B_285),'#skF_7')
      | r1_tarski('#skF_9',B_285) ) ),
    inference(resolution,[status(thm)],[c_128,c_1239])).

tff(c_2669,plain,(
    ! [B_132] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_9',B_132)) = k1_funct_1('#skF_9','#skF_1'('#skF_9',B_132))
      | ~ r1_tarski('#skF_9','#skF_9')
      | r1_tarski('#skF_9',B_132)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_323,c_2661])).

tff(c_2863,plain,(
    ! [B_290] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_9',B_290)) = k1_funct_1('#skF_9','#skF_1'('#skF_9',B_290))
      | r1_tarski('#skF_9',B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_2669])).

tff(c_2894,plain,(
    ! [B_290] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_290),k1_funct_1('#skF_9','#skF_1'('#skF_9',B_290))),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_290),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | r1_tarski('#skF_9',B_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2863,c_38])).

tff(c_6489,plain,(
    ! [B_393] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_393),k1_funct_1('#skF_9','#skF_1'('#skF_9',B_393))),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_393),'#skF_7')
      | r1_tarski('#skF_9',B_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_48,c_2894])).

tff(c_6508,plain,(
    ! [B_123] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_123),'#skF_2'('#skF_9',B_123)),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_123),'#skF_7')
      | r1_tarski('#skF_9',B_123)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski('#skF_9','#skF_9')
      | r1_tarski('#skF_9',B_123)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_6489])).

tff(c_6531,plain,(
    ! [B_394] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_394),'#skF_2'('#skF_9',B_394)),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_394),'#skF_7')
      | r1_tarski('#skF_9',B_394) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_60,c_58,c_6508])).

tff(c_6537,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_1'('#skF_9','#skF_10'),'#skF_7')
    | r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_6531,c_10])).

tff(c_6552,plain,
    ( ~ r2_hidden('#skF_1'('#skF_9','#skF_10'),'#skF_7')
    | r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6537])).

tff(c_6553,plain,(
    ~ r2_hidden('#skF_1'('#skF_9','#skF_10'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_2721,c_6552])).

tff(c_6568,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | r1_tarski('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_323,c_6553])).

tff(c_6578,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_6568])).

tff(c_6580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2721,c_6578])).

tff(c_6581,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2651])).

tff(c_6658,plain,
    ( '#skF_10' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_6581,c_2])).

tff(c_6673,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_6658])).

tff(c_6583,plain,(
    ! [B_395] :
      ( k1_funct_1('#skF_10','#skF_1'('#skF_9',B_395)) = k1_funct_1('#skF_9','#skF_1'('#skF_9',B_395))
      | r1_tarski('#skF_9',B_395) ) ),
    inference(resolution,[status(thm)],[c_128,c_2661])).

tff(c_6614,plain,(
    ! [B_395] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_395),k1_funct_1('#skF_9','#skF_1'('#skF_9',B_395))),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_395),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | r1_tarski('#skF_9',B_395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6583,c_38])).

tff(c_15667,plain,(
    ! [B_572] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_572),k1_funct_1('#skF_9','#skF_1'('#skF_9',B_572))),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_572),'#skF_7')
      | r1_tarski('#skF_9',B_572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_48,c_6614])).

tff(c_15686,plain,(
    ! [B_123] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_123),'#skF_2'('#skF_9',B_123)),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_123),'#skF_7')
      | r1_tarski('#skF_9',B_123)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski('#skF_9','#skF_9')
      | r1_tarski('#skF_9',B_123)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_15667])).

tff(c_15709,plain,(
    ! [B_573] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_9',B_573),'#skF_2'('#skF_9',B_573)),'#skF_10')
      | ~ r2_hidden('#skF_1'('#skF_9',B_573),'#skF_7')
      | r1_tarski('#skF_9',B_573) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_60,c_58,c_15686])).

tff(c_15715,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_1'('#skF_9','#skF_10'),'#skF_7')
    | r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_15709,c_10])).

tff(c_15730,plain,
    ( ~ r2_hidden('#skF_1'('#skF_9','#skF_10'),'#skF_7')
    | r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_15715])).

tff(c_15731,plain,(
    ~ r2_hidden('#skF_1'('#skF_9','#skF_10'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_6673,c_15730])).

tff(c_15749,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | r1_tarski('#skF_9','#skF_10')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_323,c_15731])).

tff(c_15763,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_15749])).

tff(c_15765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6673,c_15763])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.33/4.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.33/4.20  
% 11.33/4.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.33/4.20  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 11.33/4.20  
% 11.33/4.20  %Foreground sorts:
% 11.33/4.20  
% 11.33/4.20  
% 11.33/4.20  %Background operators:
% 11.33/4.20  
% 11.33/4.20  
% 11.33/4.20  %Foreground operators:
% 11.33/4.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.33/4.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.33/4.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.33/4.20  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.33/4.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.33/4.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.33/4.20  tff('#skF_7', type, '#skF_7': $i).
% 11.33/4.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.33/4.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.33/4.20  tff('#skF_10', type, '#skF_10': $i).
% 11.33/4.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.33/4.20  tff('#skF_9', type, '#skF_9': $i).
% 11.33/4.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.33/4.20  tff('#skF_8', type, '#skF_8': $i).
% 11.33/4.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.33/4.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.33/4.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.33/4.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.33/4.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.33/4.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 11.33/4.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.33/4.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.33/4.20  
% 11.33/4.22  tff(f_112, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (((((A = k2_relat_1(B)) & (k1_relat_1(C) = A)) & (k1_relat_1(D) = A)) & (k5_relat_1(B, C) = k5_relat_1(B, D))) => (C = D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_1)).
% 11.33/4.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.33/4.22  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 11.33/4.22  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 11.33/4.22  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 11.33/4.22  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 11.33/4.22  tff(f_87, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 11.33/4.22  tff(c_44, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_56, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.33/4.22  tff(c_48, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_12, plain, (![A_3, B_13]: (r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), A_3) | r1_tarski(A_3, B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.33/4.22  tff(c_154, plain, (![C_102, D_103, B_104, A_105]: (r2_hidden(k4_tarski(C_102, D_103), B_104) | ~r2_hidden(k4_tarski(C_102, D_103), A_105) | ~r1_tarski(A_105, B_104) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.33/4.22  tff(c_263, plain, (![A_122, B_123, B_124]: (r2_hidden(k4_tarski('#skF_1'(A_122, B_123), '#skF_2'(A_122, B_123)), B_124) | ~r1_tarski(A_122, B_124) | r1_tarski(A_122, B_123) | ~v1_relat_1(A_122))), inference(resolution, [status(thm)], [c_12, c_154])).
% 11.33/4.22  tff(c_16, plain, (![A_20, C_22, B_21]: (r2_hidden(A_20, k1_relat_1(C_22)) | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.33/4.22  tff(c_315, plain, (![A_131, B_132, B_133]: (r2_hidden('#skF_1'(A_131, B_132), k1_relat_1(B_133)) | ~v1_relat_1(B_133) | ~r1_tarski(A_131, B_133) | r1_tarski(A_131, B_132) | ~v1_relat_1(A_131))), inference(resolution, [status(thm)], [c_263, c_16])).
% 11.33/4.22  tff(c_321, plain, (![A_131, B_132]: (r2_hidden('#skF_1'(A_131, B_132), '#skF_7') | ~v1_relat_1('#skF_10') | ~r1_tarski(A_131, '#skF_10') | r1_tarski(A_131, B_132) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_48, c_315])).
% 11.33/4.22  tff(c_325, plain, (![A_131, B_132]: (r2_hidden('#skF_1'(A_131, B_132), '#skF_7') | ~r1_tarski(A_131, '#skF_10') | r1_tarski(A_131, B_132) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_321])).
% 11.33/4.22  tff(c_60, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_58, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_50, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_54, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_93, plain, (![A_86, B_87]: (r2_hidden(k4_tarski('#skF_1'(A_86, B_87), '#skF_2'(A_86, B_87)), A_86) | r1_tarski(A_86, B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.33/4.22  tff(c_120, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95), k1_relat_1(A_94)) | r1_tarski(A_94, B_95) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_93, c_16])).
% 11.33/4.22  tff(c_126, plain, (![B_95]: (r2_hidden('#skF_1'('#skF_10', B_95), '#skF_7') | r1_tarski('#skF_10', B_95) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_120])).
% 11.33/4.22  tff(c_130, plain, (![B_95]: (r2_hidden('#skF_1'('#skF_10', B_95), '#skF_7') | r1_tarski('#skF_10', B_95))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_126])).
% 11.33/4.22  tff(c_64, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_52, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_182, plain, (![A_108, C_109]: (k1_funct_1(A_108, '#skF_6'(A_108, k2_relat_1(A_108), C_109))=C_109 | ~r2_hidden(C_109, k2_relat_1(A_108)) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.33/4.22  tff(c_201, plain, (![C_109]: (k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_109))=C_109 | ~r2_hidden(C_109, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_182])).
% 11.33/4.22  tff(c_207, plain, (![C_109]: (k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_109))=C_109 | ~r2_hidden(C_109, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_201])).
% 11.33/4.22  tff(c_46, plain, (k5_relat_1('#skF_8', '#skF_10')=k5_relat_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.33/4.22  tff(c_230, plain, (![A_111, C_112]: (r2_hidden('#skF_6'(A_111, k2_relat_1(A_111), C_112), k1_relat_1(A_111)) | ~r2_hidden(C_112, k2_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.33/4.22  tff(c_239, plain, (![C_112]: (r2_hidden('#skF_6'('#skF_8', '#skF_7', C_112), k1_relat_1('#skF_8')) | ~r2_hidden(C_112, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_230])).
% 11.33/4.22  tff(c_245, plain, (![C_112]: (r2_hidden('#skF_6'('#skF_8', '#skF_7', C_112), k1_relat_1('#skF_8')) | ~r2_hidden(C_112, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_239])).
% 11.33/4.22  tff(c_530, plain, (![B_164, C_165, A_166]: (k1_funct_1(k5_relat_1(B_164, C_165), A_166)=k1_funct_1(C_165, k1_funct_1(B_164, A_166)) | ~r2_hidden(A_166, k1_relat_1(B_164)) | ~v1_funct_1(C_165) | ~v1_relat_1(C_165) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.33/4.22  tff(c_554, plain, (![C_165, C_112]: (k1_funct_1(k5_relat_1('#skF_8', C_165), '#skF_6'('#skF_8', '#skF_7', C_112))=k1_funct_1(C_165, k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_112))) | ~v1_funct_1(C_165) | ~v1_relat_1(C_165) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_112, '#skF_7'))), inference(resolution, [status(thm)], [c_245, c_530])).
% 11.33/4.22  tff(c_1012, plain, (![C_223, C_224]: (k1_funct_1(k5_relat_1('#skF_8', C_223), '#skF_6'('#skF_8', '#skF_7', C_224))=k1_funct_1(C_223, k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_224))) | ~v1_funct_1(C_223) | ~v1_relat_1(C_223) | ~r2_hidden(C_224, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_554])).
% 11.33/4.22  tff(c_1040, plain, (![C_224]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_9'), '#skF_6'('#skF_8', '#skF_7', C_224))=k1_funct_1('#skF_10', k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_224))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_224, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1012])).
% 11.33/4.22  tff(c_1110, plain, (![C_229]: (k1_funct_1(k5_relat_1('#skF_8', '#skF_9'), '#skF_6'('#skF_8', '#skF_7', C_229))=k1_funct_1('#skF_10', k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_229))) | ~r2_hidden(C_229, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1040])).
% 11.33/4.22  tff(c_579, plain, (![C_165, C_112]: (k1_funct_1(k5_relat_1('#skF_8', C_165), '#skF_6'('#skF_8', '#skF_7', C_112))=k1_funct_1(C_165, k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_112))) | ~v1_funct_1(C_165) | ~v1_relat_1(C_165) | ~r2_hidden(C_112, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_554])).
% 11.33/4.22  tff(c_1116, plain, (![C_229]: (k1_funct_1('#skF_10', k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_229)))=k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_229))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_229, '#skF_7') | ~r2_hidden(C_229, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1110, c_579])).
% 11.33/4.22  tff(c_1149, plain, (![C_230]: (k1_funct_1('#skF_10', k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_230)))=k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_230))) | ~r2_hidden(C_230, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1116])).
% 11.33/4.22  tff(c_1194, plain, (![C_231]: (k1_funct_1('#skF_9', k1_funct_1('#skF_8', '#skF_6'('#skF_8', '#skF_7', C_231)))=k1_funct_1('#skF_10', C_231) | ~r2_hidden(C_231, '#skF_7') | ~r2_hidden(C_231, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_1149])).
% 11.33/4.22  tff(c_1239, plain, (![C_232]: (k1_funct_1('#skF_10', C_232)=k1_funct_1('#skF_9', C_232) | ~r2_hidden(C_232, '#skF_7') | ~r2_hidden(C_232, '#skF_7') | ~r2_hidden(C_232, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_1194])).
% 11.33/4.22  tff(c_2246, plain, (![B_267]: (k1_funct_1('#skF_10', '#skF_1'('#skF_10', B_267))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', B_267)) | ~r2_hidden('#skF_1'('#skF_10', B_267), '#skF_7') | r1_tarski('#skF_10', B_267))), inference(resolution, [status(thm)], [c_130, c_1239])).
% 11.33/4.22  tff(c_2250, plain, (![B_132]: (k1_funct_1('#skF_10', '#skF_1'('#skF_10', B_132))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', B_132)) | ~r1_tarski('#skF_10', '#skF_10') | r1_tarski('#skF_10', B_132) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_325, c_2246])).
% 11.33/4.22  tff(c_2265, plain, (![B_268]: (k1_funct_1('#skF_10', '#skF_1'('#skF_10', B_268))=k1_funct_1('#skF_9', '#skF_1'('#skF_10', B_268)) | r1_tarski('#skF_10', B_268))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6, c_2250])).
% 11.33/4.22  tff(c_40, plain, (![C_69, A_67, B_68]: (k1_funct_1(C_69, A_67)=B_68 | ~r2_hidden(k4_tarski(A_67, B_68), C_69) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.33/4.22  tff(c_281, plain, (![B_124, A_122, B_123]: (k1_funct_1(B_124, '#skF_1'(A_122, B_123))='#skF_2'(A_122, B_123) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~r1_tarski(A_122, B_124) | r1_tarski(A_122, B_123) | ~v1_relat_1(A_122))), inference(resolution, [status(thm)], [c_263, c_40])).
% 11.33/4.22  tff(c_2278, plain, (![B_268]: (k1_funct_1('#skF_9', '#skF_1'('#skF_10', B_268))='#skF_2'('#skF_10', B_268) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r1_tarski('#skF_10', '#skF_10') | r1_tarski('#skF_10', B_268) | ~v1_relat_1('#skF_10') | r1_tarski('#skF_10', B_268))), inference(superposition, [status(thm), theory('equality')], [c_2265, c_281])).
% 11.33/4.22  tff(c_2332, plain, (![B_269]: (k1_funct_1('#skF_9', '#skF_1'('#skF_10', B_269))='#skF_2'('#skF_10', B_269) | r1_tarski('#skF_10', B_269))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6, c_56, c_54, c_2278])).
% 11.33/4.22  tff(c_38, plain, (![A_67, C_69]: (r2_hidden(k4_tarski(A_67, k1_funct_1(C_69, A_67)), C_69) | ~r2_hidden(A_67, k1_relat_1(C_69)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.33/4.22  tff(c_2357, plain, (![B_269]: (r2_hidden(k4_tarski('#skF_1'('#skF_10', B_269), '#skF_2'('#skF_10', B_269)), '#skF_9') | ~r2_hidden('#skF_1'('#skF_10', B_269), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | r1_tarski('#skF_10', B_269))), inference(superposition, [status(thm), theory('equality')], [c_2332, c_38])).
% 11.33/4.22  tff(c_2630, plain, (![B_284]: (r2_hidden(k4_tarski('#skF_1'('#skF_10', B_284), '#skF_2'('#skF_10', B_284)), '#skF_9') | ~r2_hidden('#skF_1'('#skF_10', B_284), '#skF_7') | r1_tarski('#skF_10', B_284))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_2357])).
% 11.33/4.22  tff(c_10, plain, (![A_3, B_13]: (~r2_hidden(k4_tarski('#skF_1'(A_3, B_13), '#skF_2'(A_3, B_13)), B_13) | r1_tarski(A_3, B_13) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.33/4.22  tff(c_2636, plain, (~v1_relat_1('#skF_10') | ~r2_hidden('#skF_1'('#skF_10', '#skF_9'), '#skF_7') | r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_2630, c_10])).
% 11.33/4.22  tff(c_2651, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_9'), '#skF_7') | r1_tarski('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2636])).
% 11.33/4.22  tff(c_2680, plain, (~r2_hidden('#skF_1'('#skF_10', '#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_2651])).
% 11.33/4.22  tff(c_2683, plain, (~r1_tarski('#skF_10', '#skF_10') | r1_tarski('#skF_10', '#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_325, c_2680])).
% 11.33/4.22  tff(c_2692, plain, (r1_tarski('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6, c_2683])).
% 11.33/4.22  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.33/4.22  tff(c_2706, plain, ('#skF_10'='#skF_9' | ~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_2692, c_2])).
% 11.33/4.22  tff(c_2721, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_44, c_2706])).
% 11.33/4.22  tff(c_318, plain, (![A_131, B_132]: (r2_hidden('#skF_1'(A_131, B_132), '#skF_7') | ~v1_relat_1('#skF_9') | ~r1_tarski(A_131, '#skF_9') | r1_tarski(A_131, B_132) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_50, c_315])).
% 11.33/4.22  tff(c_323, plain, (![A_131, B_132]: (r2_hidden('#skF_1'(A_131, B_132), '#skF_7') | ~r1_tarski(A_131, '#skF_9') | r1_tarski(A_131, B_132) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_318])).
% 11.33/4.22  tff(c_123, plain, (![B_95]: (r2_hidden('#skF_1'('#skF_9', B_95), '#skF_7') | r1_tarski('#skF_9', B_95) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_120])).
% 11.33/4.22  tff(c_128, plain, (![B_95]: (r2_hidden('#skF_1'('#skF_9', B_95), '#skF_7') | r1_tarski('#skF_9', B_95))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_123])).
% 11.33/4.22  tff(c_2661, plain, (![B_285]: (k1_funct_1('#skF_10', '#skF_1'('#skF_9', B_285))=k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_285)) | ~r2_hidden('#skF_1'('#skF_9', B_285), '#skF_7') | r1_tarski('#skF_9', B_285))), inference(resolution, [status(thm)], [c_128, c_1239])).
% 11.33/4.22  tff(c_2669, plain, (![B_132]: (k1_funct_1('#skF_10', '#skF_1'('#skF_9', B_132))=k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_132)) | ~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', B_132) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_323, c_2661])).
% 11.33/4.22  tff(c_2863, plain, (![B_290]: (k1_funct_1('#skF_10', '#skF_1'('#skF_9', B_290))=k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_290)) | r1_tarski('#skF_9', B_290))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_2669])).
% 11.33/4.22  tff(c_2894, plain, (![B_290]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_290), k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_290))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_290), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | r1_tarski('#skF_9', B_290))), inference(superposition, [status(thm), theory('equality')], [c_2863, c_38])).
% 11.33/4.22  tff(c_6489, plain, (![B_393]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_393), k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_393))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_393), '#skF_7') | r1_tarski('#skF_9', B_393))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_48, c_2894])).
% 11.33/4.22  tff(c_6508, plain, (![B_123]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_123), '#skF_2'('#skF_9', B_123)), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_123), '#skF_7') | r1_tarski('#skF_9', B_123) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', B_123) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_281, c_6489])).
% 11.33/4.22  tff(c_6531, plain, (![B_394]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_394), '#skF_2'('#skF_9', B_394)), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_394), '#skF_7') | r1_tarski('#skF_9', B_394))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_60, c_58, c_6508])).
% 11.33/4.22  tff(c_6537, plain, (~v1_relat_1('#skF_9') | ~r2_hidden('#skF_1'('#skF_9', '#skF_10'), '#skF_7') | r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_6531, c_10])).
% 11.33/4.22  tff(c_6552, plain, (~r2_hidden('#skF_1'('#skF_9', '#skF_10'), '#skF_7') | r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6537])).
% 11.33/4.22  tff(c_6553, plain, (~r2_hidden('#skF_1'('#skF_9', '#skF_10'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_2721, c_6552])).
% 11.33/4.22  tff(c_6568, plain, (~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_323, c_6553])).
% 11.33/4.22  tff(c_6578, plain, (r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_6568])).
% 11.33/4.22  tff(c_6580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2721, c_6578])).
% 11.33/4.22  tff(c_6581, plain, (r1_tarski('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_2651])).
% 11.33/4.22  tff(c_6658, plain, ('#skF_10'='#skF_9' | ~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_6581, c_2])).
% 11.33/4.22  tff(c_6673, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_44, c_6658])).
% 11.33/4.22  tff(c_6583, plain, (![B_395]: (k1_funct_1('#skF_10', '#skF_1'('#skF_9', B_395))=k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_395)) | r1_tarski('#skF_9', B_395))), inference(resolution, [status(thm)], [c_128, c_2661])).
% 11.33/4.22  tff(c_6614, plain, (![B_395]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_395), k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_395))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_395), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | r1_tarski('#skF_9', B_395))), inference(superposition, [status(thm), theory('equality')], [c_6583, c_38])).
% 11.33/4.22  tff(c_15667, plain, (![B_572]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_572), k1_funct_1('#skF_9', '#skF_1'('#skF_9', B_572))), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_572), '#skF_7') | r1_tarski('#skF_9', B_572))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_48, c_6614])).
% 11.33/4.22  tff(c_15686, plain, (![B_123]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_123), '#skF_2'('#skF_9', B_123)), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_123), '#skF_7') | r1_tarski('#skF_9', B_123) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', B_123) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_281, c_15667])).
% 11.33/4.22  tff(c_15709, plain, (![B_573]: (r2_hidden(k4_tarski('#skF_1'('#skF_9', B_573), '#skF_2'('#skF_9', B_573)), '#skF_10') | ~r2_hidden('#skF_1'('#skF_9', B_573), '#skF_7') | r1_tarski('#skF_9', B_573))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_60, c_58, c_15686])).
% 11.33/4.22  tff(c_15715, plain, (~v1_relat_1('#skF_9') | ~r2_hidden('#skF_1'('#skF_9', '#skF_10'), '#skF_7') | r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_15709, c_10])).
% 11.33/4.22  tff(c_15730, plain, (~r2_hidden('#skF_1'('#skF_9', '#skF_10'), '#skF_7') | r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_15715])).
% 11.33/4.22  tff(c_15731, plain, (~r2_hidden('#skF_1'('#skF_9', '#skF_10'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_6673, c_15730])).
% 11.33/4.22  tff(c_15749, plain, (~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', '#skF_10') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_323, c_15731])).
% 11.33/4.22  tff(c_15763, plain, (r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_15749])).
% 11.33/4.22  tff(c_15765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6673, c_15763])).
% 11.33/4.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.33/4.22  
% 11.33/4.22  Inference rules
% 11.33/4.22  ----------------------
% 11.33/4.22  #Ref     : 5
% 11.33/4.22  #Sup     : 3387
% 11.33/4.22  #Fact    : 0
% 11.33/4.22  #Define  : 0
% 11.33/4.22  #Split   : 14
% 11.33/4.22  #Chain   : 0
% 11.33/4.22  #Close   : 0
% 11.33/4.22  
% 11.33/4.22  Ordering : KBO
% 11.33/4.22  
% 11.33/4.22  Simplification rules
% 11.33/4.22  ----------------------
% 11.33/4.22  #Subsume      : 839
% 11.33/4.22  #Demod        : 5510
% 11.33/4.22  #Tautology    : 777
% 11.33/4.22  #SimpNegUnit  : 9
% 11.33/4.22  #BackRed      : 20
% 11.33/4.22  
% 11.33/4.22  #Partial instantiations: 0
% 11.33/4.22  #Strategies tried      : 1
% 11.33/4.22  
% 11.33/4.22  Timing (in seconds)
% 11.33/4.22  ----------------------
% 11.33/4.22  Preprocessing        : 0.31
% 11.33/4.22  Parsing              : 0.15
% 11.33/4.23  CNF conversion       : 0.03
% 11.33/4.23  Main loop            : 3.07
% 11.33/4.23  Inferencing          : 1.00
% 11.33/4.23  Reduction            : 0.99
% 11.33/4.23  Demodulation         : 0.71
% 11.33/4.23  BG Simplification    : 0.11
% 11.33/4.23  Subsumption          : 0.77
% 11.33/4.23  Abstraction          : 0.15
% 11.33/4.23  MUC search           : 0.00
% 11.33/4.23  Cooper               : 0.00
% 11.33/4.23  Total                : 3.43
% 11.33/4.23  Index Insertion      : 0.00
% 11.33/4.23  Index Deletion       : 0.00
% 11.33/4.23  Index Matching       : 0.00
% 11.33/4.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
