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
% DateTime   : Thu Dec  3 10:05:38 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 163 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 481 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_1'(A_26,B_27),B_27)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_12,B_14] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_12,B_14)),k1_relat_1(A_12))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_49,plain,(
    r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_45,plain,(
    ! [C_29,B_30,A_31] :
      ( r2_hidden(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_36,B_37,B_38] :
      ( r2_hidden('#skF_1'(A_36,B_37),B_38)
      | ~ r1_tarski(A_36,B_38)
      | r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_44,B_45,B_46,B_47] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_46)
      | ~ r1_tarski(B_47,B_46)
      | ~ r1_tarski(A_44,B_47)
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_95,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_48,'#skF_5')
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_49,c_79])).

tff(c_112,plain,(
    ! [A_53,B_54,B_55] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_55)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),B_55)
      | ~ r1_tarski(A_53,'#skF_5')
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_118,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_53,'#skF_5')
      | r1_tarski(A_53,B_54)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_112])).

tff(c_127,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_56,'#skF_5')
      | r1_tarski(A_56,B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_118])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_158,plain,(
    ! [A_61] :
      ( ~ r1_tarski(A_61,'#skF_5')
      | r1_tarski(A_61,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_30,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_77,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_168,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_158,c_77])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_168])).

tff(c_177,plain,(
    r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( k10_relat_1(A_9,k1_relat_1(B_11)) = k1_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k9_relat_1(C_8,A_6),k9_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,k10_relat_1(B_16,A_15)),A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_179,plain,(
    ! [A_62,B_63,B_64,B_65] :
      ( r2_hidden('#skF_1'(A_62,B_63),B_64)
      | ~ r1_tarski(B_65,B_64)
      | ~ r1_tarski(A_62,B_65)
      | r1_tarski(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_703,plain,(
    ! [A_122,B_123,A_124,B_125] :
      ( r2_hidden('#skF_1'(A_122,B_123),A_124)
      | ~ r1_tarski(A_122,k9_relat_1(B_125,k10_relat_1(B_125,A_124)))
      | r1_tarski(A_122,B_123)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_14,c_179])).

tff(c_1075,plain,(
    ! [C_181,A_182,B_183,A_184] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_181,A_182),B_183),A_184)
      | r1_tarski(k9_relat_1(C_181,A_182),B_183)
      | ~ v1_funct_1(C_181)
      | ~ r1_tarski(A_182,k10_relat_1(C_181,A_184))
      | ~ v1_relat_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_8,c_703])).

tff(c_1093,plain,(
    ! [C_189,A_190,A_191] :
      ( r1_tarski(k9_relat_1(C_189,A_190),A_191)
      | ~ v1_funct_1(C_189)
      | ~ r1_tarski(A_190,k10_relat_1(C_189,A_191))
      | ~ v1_relat_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_1075,c_4])).

tff(c_176,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_178,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_1121,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1093,c_178])).

tff(c_1134,plain,(
    ~ r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_1121])).

tff(c_1137,plain,
    ( ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1134])).

tff(c_1140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_49,c_1137])).

tff(c_1142,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1169,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_1142,c_26])).

tff(c_1141,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_28,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1193,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_1142,c_28])).

tff(c_1227,plain,(
    ! [A_207,C_208,B_209] :
      ( r1_tarski(A_207,k10_relat_1(C_208,B_209))
      | ~ r1_tarski(k9_relat_1(C_208,A_207),B_209)
      | ~ r1_tarski(A_207,k1_relat_1(C_208))
      | ~ v1_funct_1(C_208)
      | ~ v1_relat_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1238,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1193,c_1227])).

tff(c_1260,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_1141,c_1238])).

tff(c_1273,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1260])).

tff(c_1276,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_1273])).

tff(c_1278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1169,c_1276])).

tff(c_1280,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1294,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1280,c_32])).

tff(c_1279,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1281,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1280,c_34])).

tff(c_1450,plain,(
    ! [A_249,C_250,B_251] :
      ( r1_tarski(A_249,k10_relat_1(C_250,B_251))
      | ~ r1_tarski(k9_relat_1(C_250,A_249),B_251)
      | ~ r1_tarski(A_249,k1_relat_1(C_250))
      | ~ v1_funct_1(C_250)
      | ~ v1_relat_1(C_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1472,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1281,c_1450])).

tff(c_1488,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_1279,c_1472])).

tff(c_1496,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1488])).

tff(c_1500,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_1496])).

tff(c_1502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1294,c_1500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:58:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.70  
% 3.92/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.70  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.92/1.70  
% 3.92/1.70  %Foreground sorts:
% 3.92/1.70  
% 3.92/1.70  
% 3.92/1.70  %Background operators:
% 3.92/1.70  
% 3.92/1.70  
% 3.92/1.70  %Foreground operators:
% 3.92/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.92/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.92/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.92/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.92/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.92/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.92/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.92/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.92/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.92/1.70  
% 3.92/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.92/1.72  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 3.92/1.72  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.92/1.72  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.92/1.72  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.92/1.72  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.92/1.72  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.92/1.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_38, plain, (![A_26, B_27]: (~r2_hidden('#skF_1'(A_26, B_27), B_27) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_43, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_38])).
% 3.92/1.72  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_12, plain, (![A_12, B_14]: (r1_tarski(k1_relat_1(k5_relat_1(A_12, B_14)), k1_relat_1(A_12)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.92/1.72  tff(c_36, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_49, plain, (r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_36])).
% 3.92/1.72  tff(c_45, plain, (![C_29, B_30, A_31]: (r2_hidden(C_29, B_30) | ~r2_hidden(C_29, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_54, plain, (![A_36, B_37, B_38]: (r2_hidden('#skF_1'(A_36, B_37), B_38) | ~r1_tarski(A_36, B_38) | r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_6, c_45])).
% 3.92/1.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_79, plain, (![A_44, B_45, B_46, B_47]: (r2_hidden('#skF_1'(A_44, B_45), B_46) | ~r1_tarski(B_47, B_46) | ~r1_tarski(A_44, B_47) | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_54, c_2])).
% 3.92/1.72  tff(c_95, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(A_48, '#skF_5') | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_49, c_79])).
% 3.92/1.72  tff(c_112, plain, (![A_53, B_54, B_55]: (r2_hidden('#skF_1'(A_53, B_54), B_55) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), B_55) | ~r1_tarski(A_53, '#skF_5') | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_95, c_2])).
% 3.92/1.72  tff(c_118, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), k1_relat_1('#skF_2')) | ~r1_tarski(A_53, '#skF_5') | r1_tarski(A_53, B_54) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_112])).
% 3.92/1.72  tff(c_127, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), k1_relat_1('#skF_2')) | ~r1_tarski(A_56, '#skF_5') | r1_tarski(A_56, B_57))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_118])).
% 3.92/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.72  tff(c_158, plain, (![A_61]: (~r1_tarski(A_61, '#skF_5') | r1_tarski(A_61, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_127, c_4])).
% 3.92/1.72  tff(c_30, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_77, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_30])).
% 3.92/1.72  tff(c_168, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_158, c_77])).
% 3.92/1.72  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_168])).
% 3.92/1.72  tff(c_177, plain, (r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 3.92/1.72  tff(c_10, plain, (![A_9, B_11]: (k10_relat_1(A_9, k1_relat_1(B_11))=k1_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.92/1.72  tff(c_22, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_8, plain, (![C_8, A_6, B_7]: (r1_tarski(k9_relat_1(C_8, A_6), k9_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.92/1.72  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, k10_relat_1(B_16, A_15)), A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.92/1.72  tff(c_179, plain, (![A_62, B_63, B_64, B_65]: (r2_hidden('#skF_1'(A_62, B_63), B_64) | ~r1_tarski(B_65, B_64) | ~r1_tarski(A_62, B_65) | r1_tarski(A_62, B_63))), inference(resolution, [status(thm)], [c_54, c_2])).
% 3.92/1.72  tff(c_703, plain, (![A_122, B_123, A_124, B_125]: (r2_hidden('#skF_1'(A_122, B_123), A_124) | ~r1_tarski(A_122, k9_relat_1(B_125, k10_relat_1(B_125, A_124))) | r1_tarski(A_122, B_123) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_14, c_179])).
% 3.92/1.72  tff(c_1075, plain, (![C_181, A_182, B_183, A_184]: (r2_hidden('#skF_1'(k9_relat_1(C_181, A_182), B_183), A_184) | r1_tarski(k9_relat_1(C_181, A_182), B_183) | ~v1_funct_1(C_181) | ~r1_tarski(A_182, k10_relat_1(C_181, A_184)) | ~v1_relat_1(C_181))), inference(resolution, [status(thm)], [c_8, c_703])).
% 3.92/1.72  tff(c_1093, plain, (![C_189, A_190, A_191]: (r1_tarski(k9_relat_1(C_189, A_190), A_191) | ~v1_funct_1(C_189) | ~r1_tarski(A_190, k10_relat_1(C_189, A_191)) | ~v1_relat_1(C_189))), inference(resolution, [status(thm)], [c_1075, c_4])).
% 3.92/1.72  tff(c_176, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 3.92/1.72  tff(c_178, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_176])).
% 3.92/1.72  tff(c_1121, plain, (~v1_funct_1('#skF_2') | ~r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1093, c_178])).
% 3.92/1.72  tff(c_1134, plain, (~r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_1121])).
% 3.92/1.72  tff(c_1137, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1134])).
% 3.92/1.72  tff(c_1140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_49, c_1137])).
% 3.92/1.72  tff(c_1142, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_176])).
% 3.92/1.72  tff(c_26, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_1169, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_1142, c_26])).
% 3.92/1.72  tff(c_1141, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_176])).
% 3.92/1.72  tff(c_28, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_1193, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_1142, c_28])).
% 3.92/1.72  tff(c_1227, plain, (![A_207, C_208, B_209]: (r1_tarski(A_207, k10_relat_1(C_208, B_209)) | ~r1_tarski(k9_relat_1(C_208, A_207), B_209) | ~r1_tarski(A_207, k1_relat_1(C_208)) | ~v1_funct_1(C_208) | ~v1_relat_1(C_208))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.92/1.72  tff(c_1238, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1193, c_1227])).
% 3.92/1.72  tff(c_1260, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_1141, c_1238])).
% 3.92/1.72  tff(c_1273, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1260])).
% 3.92/1.72  tff(c_1276, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_1273])).
% 3.92/1.72  tff(c_1278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1169, c_1276])).
% 3.92/1.72  tff(c_1280, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_36])).
% 3.92/1.72  tff(c_32, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_1294, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1280, c_32])).
% 3.92/1.72  tff(c_1279, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_36])).
% 3.92/1.72  tff(c_34, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.92/1.72  tff(c_1281, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1280, c_34])).
% 3.92/1.72  tff(c_1450, plain, (![A_249, C_250, B_251]: (r1_tarski(A_249, k10_relat_1(C_250, B_251)) | ~r1_tarski(k9_relat_1(C_250, A_249), B_251) | ~r1_tarski(A_249, k1_relat_1(C_250)) | ~v1_funct_1(C_250) | ~v1_relat_1(C_250))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.92/1.72  tff(c_1472, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1281, c_1450])).
% 3.92/1.72  tff(c_1488, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_1279, c_1472])).
% 3.92/1.72  tff(c_1496, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1488])).
% 3.92/1.72  tff(c_1500, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_1496])).
% 3.92/1.72  tff(c_1502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1294, c_1500])).
% 3.92/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.72  
% 3.92/1.72  Inference rules
% 3.92/1.72  ----------------------
% 3.92/1.72  #Ref     : 0
% 3.92/1.72  #Sup     : 355
% 3.92/1.72  #Fact    : 0
% 3.92/1.72  #Define  : 0
% 3.92/1.72  #Split   : 10
% 3.92/1.72  #Chain   : 0
% 3.92/1.72  #Close   : 0
% 3.92/1.72  
% 3.92/1.72  Ordering : KBO
% 3.92/1.72  
% 3.92/1.72  Simplification rules
% 3.92/1.72  ----------------------
% 3.92/1.72  #Subsume      : 83
% 3.92/1.72  #Demod        : 61
% 3.92/1.72  #Tautology    : 18
% 3.92/1.72  #SimpNegUnit  : 4
% 3.92/1.72  #BackRed      : 0
% 3.92/1.72  
% 3.92/1.72  #Partial instantiations: 0
% 3.92/1.72  #Strategies tried      : 1
% 3.92/1.72  
% 3.92/1.72  Timing (in seconds)
% 3.92/1.72  ----------------------
% 3.92/1.72  Preprocessing        : 0.30
% 3.92/1.72  Parsing              : 0.16
% 3.92/1.72  CNF conversion       : 0.02
% 3.92/1.72  Main loop            : 0.63
% 3.92/1.72  Inferencing          : 0.21
% 3.92/1.72  Reduction            : 0.16
% 3.92/1.72  Demodulation         : 0.11
% 3.92/1.72  BG Simplification    : 0.02
% 3.92/1.72  Subsumption          : 0.20
% 3.92/1.72  Abstraction          : 0.03
% 3.92/1.72  MUC search           : 0.00
% 3.92/1.72  Cooper               : 0.00
% 3.92/1.72  Total                : 0.97
% 3.92/1.72  Index Insertion      : 0.00
% 3.92/1.72  Index Deletion       : 0.00
% 3.92/1.72  Index Matching       : 0.00
% 3.92/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
