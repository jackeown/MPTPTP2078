%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:16 EST 2020

% Result     : Theorem 9.35s
% Output     : CNFRefutation 9.35s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 156 expanded)
%              Number of leaves         :   29 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 459 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
            <=> ( r2_hidden(A,k1_relat_1(C))
                & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,
    ( r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_70,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,
    ( r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_91,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_116,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_91,c_46])).

tff(c_28,plain,(
    ! [A_31,B_33] :
      ( k10_relat_1(A_31,k1_relat_1(B_33)) = k1_relat_1(k5_relat_1(A_31,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_152,plain,(
    ! [A_86,C_87] :
      ( r2_hidden(k4_tarski(A_86,k1_funct_1(C_87,A_86)),C_87)
      | ~ r2_hidden(A_86,k1_relat_1(C_87))
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_775,plain,(
    ! [A_155,C_156,B_157] :
      ( r2_hidden(k4_tarski(A_155,k1_funct_1(C_156,A_155)),B_157)
      | ~ r1_tarski(C_156,B_157)
      | ~ r2_hidden(A_155,k1_relat_1(C_156))
      | ~ v1_funct_1(C_156)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k2_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(D_24,C_21),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_812,plain,(
    ! [C_156,A_155,B_157] :
      ( r2_hidden(k1_funct_1(C_156,A_155),k2_relat_1(B_157))
      | ~ r1_tarski(C_156,B_157)
      | ~ r2_hidden(A_155,k1_relat_1(C_156))
      | ~ v1_funct_1(C_156)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_775,c_10])).

tff(c_32,plain,(
    ! [A_37,C_39] :
      ( r2_hidden(k4_tarski(A_37,k1_funct_1(C_39,A_37)),C_39)
      | ~ r2_hidden(A_37,k1_relat_1(C_39))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_814,plain,(
    ! [A_158,C_159,B_160,D_161] :
      ( r2_hidden(A_158,k10_relat_1(C_159,B_160))
      | ~ r2_hidden(D_161,B_160)
      | ~ r2_hidden(k4_tarski(A_158,D_161),C_159)
      | ~ r2_hidden(D_161,k2_relat_1(C_159))
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1010,plain,(
    ! [A_169,C_170] :
      ( r2_hidden(A_169,k10_relat_1(C_170,k1_relat_1('#skF_8')))
      | ~ r2_hidden(k4_tarski(A_169,k1_funct_1('#skF_9','#skF_7')),C_170)
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1(C_170))
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_91,c_814])).

tff(c_1030,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8')))
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_1010])).

tff(c_1043,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8')))
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_70,c_1030])).

tff(c_1045,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k2_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1043])).

tff(c_1048,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_812,c_1045])).

tff(c_1061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_70,c_63,c_1048])).

tff(c_1062,plain,(
    r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_1043])).

tff(c_1082,plain,
    ( r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1062])).

tff(c_1092,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_1082])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_1092])).

tff(c_1095,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1096,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1152,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden(k4_tarski(A_190,'#skF_6'(A_190,B_191,C_192)),C_192)
      | ~ r2_hidden(A_190,k10_relat_1(C_192,B_191))
      | ~ v1_relat_1(C_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [C_39,A_37,B_38] :
      ( k1_funct_1(C_39,A_37) = B_38
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1321,plain,(
    ! [C_221,A_222,B_223] :
      ( k1_funct_1(C_221,A_222) = '#skF_6'(A_222,B_223,C_221)
      | ~ v1_funct_1(C_221)
      | ~ r2_hidden(A_222,k10_relat_1(C_221,B_223))
      | ~ v1_relat_1(C_221) ) ),
    inference(resolution,[status(thm)],[c_1152,c_34])).

tff(c_8137,plain,(
    ! [A_726,B_727,A_728] :
      ( '#skF_6'(A_726,k1_relat_1(B_727),A_728) = k1_funct_1(A_728,A_726)
      | ~ v1_funct_1(A_728)
      | ~ r2_hidden(A_726,k1_relat_1(k5_relat_1(A_728,B_727)))
      | ~ v1_relat_1(A_728)
      | ~ v1_relat_1(B_727)
      | ~ v1_relat_1(A_728) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1321])).

tff(c_8339,plain,
    ( '#skF_6'('#skF_7',k1_relat_1('#skF_8'),'#skF_9') = k1_funct_1('#skF_9','#skF_7')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1095,c_8137])).

tff(c_8402,plain,(
    '#skF_6'('#skF_7',k1_relat_1('#skF_8'),'#skF_9') = k1_funct_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_38,c_8339])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden('#skF_6'(A_25,B_26,C_27),B_26)
      | ~ r2_hidden(A_25,k10_relat_1(C_27,B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8435,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8')))
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_8402,c_22])).

tff(c_8457,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_7'),k1_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8435])).

tff(c_8458,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_9',k1_relat_1('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1096,c_8457])).

tff(c_8462,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8')))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8458])).

tff(c_8465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_1095,c_8462])).

tff(c_8467,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8486,plain,(
    ! [A_731,B_732] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_731,B_732)),k1_relat_1(A_731))
      | ~ v1_relat_1(B_732)
      | ~ v1_relat_1(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8466,plain,(
    r2_hidden('#skF_7',k1_relat_1(k5_relat_1('#skF_9','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8471,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_7',B_2)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_9','#skF_8')),B_2) ) ),
    inference(resolution,[status(thm)],[c_8466,c_2])).

tff(c_8490,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_8486,c_8471])).

tff(c_8493,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_8490])).

tff(c_8495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8467,c_8493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:11:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.35/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.35/3.06  
% 9.35/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.35/3.07  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 9.35/3.07  
% 9.35/3.07  %Foreground sorts:
% 9.35/3.07  
% 9.35/3.07  
% 9.35/3.07  %Background operators:
% 9.35/3.07  
% 9.35/3.07  
% 9.35/3.07  %Foreground operators:
% 9.35/3.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.35/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.35/3.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.35/3.07  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.35/3.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.35/3.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.35/3.07  tff('#skF_7', type, '#skF_7': $i).
% 9.35/3.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.35/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.35/3.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.35/3.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.35/3.07  tff('#skF_9', type, '#skF_9': $i).
% 9.35/3.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.35/3.07  tff('#skF_8', type, '#skF_8': $i).
% 9.35/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.35/3.07  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.35/3.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.35/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.35/3.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.35/3.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.35/3.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.35/3.07  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.35/3.07  
% 9.35/3.08  tff(f_91, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 9.35/3.08  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 9.35/3.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.35/3.08  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 9.35/3.08  tff(f_40, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 9.35/3.08  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 9.35/3.08  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 9.35/3.08  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.08  tff(c_44, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.08  tff(c_56, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.08  tff(c_70, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_56])).
% 9.35/3.08  tff(c_52, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.08  tff(c_91, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 9.35/3.08  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.08  tff(c_116, plain, (~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_91, c_46])).
% 9.35/3.08  tff(c_28, plain, (![A_31, B_33]: (k10_relat_1(A_31, k1_relat_1(B_33))=k1_relat_1(k5_relat_1(A_31, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.35/3.08  tff(c_38, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.35/3.08  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.08  tff(c_58, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.08  tff(c_63, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_58])).
% 9.35/3.08  tff(c_152, plain, (![A_86, C_87]: (r2_hidden(k4_tarski(A_86, k1_funct_1(C_87, A_86)), C_87) | ~r2_hidden(A_86, k1_relat_1(C_87)) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.35/3.08  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.35/3.08  tff(c_775, plain, (![A_155, C_156, B_157]: (r2_hidden(k4_tarski(A_155, k1_funct_1(C_156, A_155)), B_157) | ~r1_tarski(C_156, B_157) | ~r2_hidden(A_155, k1_relat_1(C_156)) | ~v1_funct_1(C_156) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_152, c_2])).
% 9.35/3.08  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k2_relat_1(A_6)) | ~r2_hidden(k4_tarski(D_24, C_21), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.35/3.08  tff(c_812, plain, (![C_156, A_155, B_157]: (r2_hidden(k1_funct_1(C_156, A_155), k2_relat_1(B_157)) | ~r1_tarski(C_156, B_157) | ~r2_hidden(A_155, k1_relat_1(C_156)) | ~v1_funct_1(C_156) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_775, c_10])).
% 9.35/3.08  tff(c_32, plain, (![A_37, C_39]: (r2_hidden(k4_tarski(A_37, k1_funct_1(C_39, A_37)), C_39) | ~r2_hidden(A_37, k1_relat_1(C_39)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.35/3.08  tff(c_814, plain, (![A_158, C_159, B_160, D_161]: (r2_hidden(A_158, k10_relat_1(C_159, B_160)) | ~r2_hidden(D_161, B_160) | ~r2_hidden(k4_tarski(A_158, D_161), C_159) | ~r2_hidden(D_161, k2_relat_1(C_159)) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.35/3.08  tff(c_1010, plain, (![A_169, C_170]: (r2_hidden(A_169, k10_relat_1(C_170, k1_relat_1('#skF_8'))) | ~r2_hidden(k4_tarski(A_169, k1_funct_1('#skF_9', '#skF_7')), C_170) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1(C_170)) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_91, c_814])).
% 9.35/3.08  tff(c_1030, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8'))) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_1010])).
% 9.35/3.08  tff(c_1043, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8'))) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_70, c_1030])).
% 9.35/3.08  tff(c_1045, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k2_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_1043])).
% 9.35/3.08  tff(c_1048, plain, (~r1_tarski('#skF_9', '#skF_9') | ~r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_812, c_1045])).
% 9.35/3.08  tff(c_1061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_70, c_63, c_1048])).
% 9.35/3.08  tff(c_1062, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_1043])).
% 9.35/3.08  tff(c_1082, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1062])).
% 9.35/3.08  tff(c_1092, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_1082])).
% 9.35/3.08  tff(c_1094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_1092])).
% 9.35/3.08  tff(c_1095, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_52])).
% 9.35/3.08  tff(c_1096, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 9.35/3.08  tff(c_1152, plain, (![A_190, B_191, C_192]: (r2_hidden(k4_tarski(A_190, '#skF_6'(A_190, B_191, C_192)), C_192) | ~r2_hidden(A_190, k10_relat_1(C_192, B_191)) | ~v1_relat_1(C_192))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.35/3.08  tff(c_34, plain, (![C_39, A_37, B_38]: (k1_funct_1(C_39, A_37)=B_38 | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.35/3.08  tff(c_1321, plain, (![C_221, A_222, B_223]: (k1_funct_1(C_221, A_222)='#skF_6'(A_222, B_223, C_221) | ~v1_funct_1(C_221) | ~r2_hidden(A_222, k10_relat_1(C_221, B_223)) | ~v1_relat_1(C_221))), inference(resolution, [status(thm)], [c_1152, c_34])).
% 9.35/3.08  tff(c_8137, plain, (![A_726, B_727, A_728]: ('#skF_6'(A_726, k1_relat_1(B_727), A_728)=k1_funct_1(A_728, A_726) | ~v1_funct_1(A_728) | ~r2_hidden(A_726, k1_relat_1(k5_relat_1(A_728, B_727))) | ~v1_relat_1(A_728) | ~v1_relat_1(B_727) | ~v1_relat_1(A_728))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1321])).
% 9.35/3.08  tff(c_8339, plain, ('#skF_6'('#skF_7', k1_relat_1('#skF_8'), '#skF_9')=k1_funct_1('#skF_9', '#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1095, c_8137])).
% 9.35/3.08  tff(c_8402, plain, ('#skF_6'('#skF_7', k1_relat_1('#skF_8'), '#skF_9')=k1_funct_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_38, c_8339])).
% 9.35/3.08  tff(c_22, plain, (![A_25, B_26, C_27]: (r2_hidden('#skF_6'(A_25, B_26, C_27), B_26) | ~r2_hidden(A_25, k10_relat_1(C_27, B_26)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.35/3.08  tff(c_8435, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8'))) | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_8402, c_22])).
% 9.35/3.08  tff(c_8457, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_7'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8435])).
% 9.35/3.08  tff(c_8458, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_9', k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_1096, c_8457])).
% 9.35/3.08  tff(c_8462, plain, (~r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8'))) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_28, c_8458])).
% 9.35/3.08  tff(c_8465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_1095, c_8462])).
% 9.35/3.08  tff(c_8467, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_56])).
% 9.35/3.08  tff(c_8486, plain, (![A_731, B_732]: (r1_tarski(k1_relat_1(k5_relat_1(A_731, B_732)), k1_relat_1(A_731)) | ~v1_relat_1(B_732) | ~v1_relat_1(A_731))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.35/3.08  tff(c_8466, plain, (r2_hidden('#skF_7', k1_relat_1(k5_relat_1('#skF_9', '#skF_8')))), inference(splitRight, [status(thm)], [c_56])).
% 9.35/3.08  tff(c_8471, plain, (![B_2]: (r2_hidden('#skF_7', B_2) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_9', '#skF_8')), B_2))), inference(resolution, [status(thm)], [c_8466, c_2])).
% 9.35/3.08  tff(c_8490, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_8486, c_8471])).
% 9.35/3.08  tff(c_8493, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_8490])).
% 9.35/3.08  tff(c_8495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8467, c_8493])).
% 9.35/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.35/3.08  
% 9.35/3.08  Inference rules
% 9.35/3.08  ----------------------
% 9.35/3.08  #Ref     : 0
% 9.35/3.08  #Sup     : 1986
% 9.35/3.08  #Fact    : 0
% 9.35/3.08  #Define  : 0
% 9.35/3.08  #Split   : 5
% 9.35/3.08  #Chain   : 0
% 9.35/3.08  #Close   : 0
% 9.35/3.08  
% 9.35/3.08  Ordering : KBO
% 9.35/3.08  
% 9.35/3.08  Simplification rules
% 9.35/3.08  ----------------------
% 9.35/3.08  #Subsume      : 165
% 9.35/3.08  #Demod        : 154
% 9.35/3.08  #Tautology    : 96
% 9.35/3.08  #SimpNegUnit  : 3
% 9.35/3.08  #BackRed      : 0
% 9.35/3.08  
% 9.35/3.08  #Partial instantiations: 0
% 9.35/3.08  #Strategies tried      : 1
% 9.35/3.08  
% 9.35/3.08  Timing (in seconds)
% 9.35/3.08  ----------------------
% 9.35/3.08  Preprocessing        : 0.34
% 9.35/3.08  Parsing              : 0.18
% 9.35/3.08  CNF conversion       : 0.03
% 9.35/3.08  Main loop            : 1.90
% 9.35/3.08  Inferencing          : 0.62
% 9.35/3.08  Reduction            : 0.43
% 9.35/3.08  Demodulation         : 0.29
% 9.35/3.08  BG Simplification    : 0.08
% 9.35/3.08  Subsumption          : 0.59
% 9.35/3.08  Abstraction          : 0.11
% 9.35/3.08  MUC search           : 0.00
% 9.35/3.08  Cooper               : 0.00
% 9.35/3.08  Total                : 2.28
% 9.35/3.08  Index Insertion      : 0.00
% 9.35/3.08  Index Deletion       : 0.00
% 9.35/3.08  Index Matching       : 0.00
% 9.35/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
