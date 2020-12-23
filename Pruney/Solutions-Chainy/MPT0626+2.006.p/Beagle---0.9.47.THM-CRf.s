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
% DateTime   : Thu Dec  3 10:03:16 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 154 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 478 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_77,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,
    ( r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
    | r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_40,plain,
    ( r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
    | r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_41,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_30,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_30])).

tff(c_47,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( k10_relat_1(A_7,k1_relat_1(B_9)) = k1_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    ! [A_34,C_35] :
      ( r2_hidden(k4_tarski(A_34,k1_funct_1(C_35,A_34)),C_35)
      | ~ r2_hidden(A_34,k1_relat_1(C_35))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [B_11,C_12,A_10] :
      ( r2_hidden(B_11,k2_relat_1(C_12))
      | ~ r2_hidden(k4_tarski(A_10,B_11),C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,(
    ! [C_35,A_34] :
      ( r2_hidden(k1_funct_1(C_35,A_34),k2_relat_1(C_35))
      | ~ r2_hidden(A_34,k1_relat_1(C_35))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_60,c_12])).

tff(c_16,plain,(
    ! [A_13,C_15] :
      ( r2_hidden(k4_tarski(A_13,k1_funct_1(C_15,A_13)),C_15)
      | ~ r2_hidden(A_13,k1_relat_1(C_15))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [A_41,C_42,B_43,D_44] :
      ( r2_hidden(A_41,k10_relat_1(C_42,B_43))
      | ~ r2_hidden(D_44,B_43)
      | ~ r2_hidden(k4_tarski(A_41,D_44),C_42)
      | ~ r2_hidden(D_44,k2_relat_1(C_42))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_222,plain,(
    ! [A_58,C_59] :
      ( r2_hidden(A_58,k10_relat_1(C_59,k1_relat_1('#skF_3')))
      | ~ r2_hidden(k4_tarski(A_58,k1_funct_1('#skF_4','#skF_2')),C_59)
      | ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k2_relat_1(C_59))
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_234,plain,
    ( r2_hidden('#skF_2',k10_relat_1('#skF_4',k1_relat_1('#skF_3')))
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k2_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_222])).

tff(c_239,plain,
    ( r2_hidden('#skF_2',k10_relat_1('#skF_4',k1_relat_1('#skF_3')))
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_41,c_234])).

tff(c_240,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_243,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_240])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_41,c_243])).

tff(c_248,plain,(
    r2_hidden('#skF_2',k10_relat_1('#skF_4',k1_relat_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_274,plain,
    ( r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_248])).

tff(c_283,plain,(
    r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_274])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_283])).

tff(c_286,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_286])).

tff(c_290,plain,(
    r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_291,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_306,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(k4_tarski(A_73,'#skF_1'(A_73,B_74,C_75)),C_75)
      | ~ r2_hidden(A_73,k10_relat_1(C_75,B_74))
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( k1_funct_1(C_15,A_13) = B_14
      | ~ r2_hidden(k4_tarski(A_13,B_14),C_15)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_353,plain,(
    ! [C_83,A_84,B_85] :
      ( k1_funct_1(C_83,A_84) = '#skF_1'(A_84,B_85,C_83)
      | ~ v1_funct_1(C_83)
      | ~ r2_hidden(A_84,k10_relat_1(C_83,B_85))
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_306,c_18])).

tff(c_533,plain,(
    ! [A_105,B_106,A_107] :
      ( '#skF_1'(A_105,k1_relat_1(B_106),A_107) = k1_funct_1(A_107,A_105)
      | ~ v1_funct_1(A_107)
      | ~ r2_hidden(A_105,k1_relat_1(k5_relat_1(A_107,B_106)))
      | ~ v1_relat_1(A_107)
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_353])).

tff(c_555,plain,
    ( '#skF_1'('#skF_2',k1_relat_1('#skF_3'),'#skF_4') = k1_funct_1('#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_290,c_533])).

tff(c_565,plain,(
    '#skF_1'('#skF_2',k1_relat_1('#skF_3'),'#skF_4') = k1_funct_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_22,c_555])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden(A_1,k10_relat_1(C_3,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_575,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_2',k10_relat_1('#skF_4',k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_4])).

tff(c_583,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_2',k10_relat_1('#skF_4',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_575])).

tff(c_584,plain,(
    ~ r2_hidden('#skF_2',k10_relat_1('#skF_4',k1_relat_1('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_583])).

tff(c_588,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_584])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_290,c_588])).

tff(c_593,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_592,plain,(
    r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_609,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_hidden(k4_tarski(A_125,'#skF_1'(A_125,B_126,C_127)),C_127)
      | ~ r2_hidden(A_125,k10_relat_1(C_127,B_126))
      | ~ v1_relat_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_10,C_12,B_11] :
      ( r2_hidden(A_10,k1_relat_1(C_12))
      | ~ r2_hidden(k4_tarski(A_10,B_11),C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_636,plain,(
    ! [A_130,C_131,B_132] :
      ( r2_hidden(A_130,k1_relat_1(C_131))
      | ~ r2_hidden(A_130,k10_relat_1(C_131,B_132))
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_609,c_14])).

tff(c_696,plain,(
    ! [A_142,A_143,B_144] :
      ( r2_hidden(A_142,k1_relat_1(A_143))
      | ~ r2_hidden(A_142,k1_relat_1(k5_relat_1(A_143,B_144)))
      | ~ v1_relat_1(A_143)
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_636])).

tff(c_711,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_592,c_696])).

tff(c_717,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_711])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.43  
% 2.61/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.43  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.61/1.43  
% 2.61/1.43  %Foreground sorts:
% 2.61/1.43  
% 2.61/1.43  
% 2.61/1.43  %Background operators:
% 2.61/1.43  
% 2.61/1.43  
% 2.61/1.43  %Foreground operators:
% 2.61/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.61/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.61/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.61/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.43  
% 2.92/1.45  tff(f_77, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 2.92/1.45  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.92/1.45  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.92/1.45  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.92/1.45  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.92/1.45  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.45  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.45  tff(c_36, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.45  tff(c_44, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.92/1.45  tff(c_40, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.45  tff(c_41, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.92/1.45  tff(c_30, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3')) | ~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.45  tff(c_46, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3')) | ~r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_30])).
% 2.92/1.45  tff(c_47, plain, (~r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_46])).
% 2.92/1.45  tff(c_10, plain, (![A_7, B_9]: (k10_relat_1(A_7, k1_relat_1(B_9))=k1_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.45  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.45  tff(c_60, plain, (![A_34, C_35]: (r2_hidden(k4_tarski(A_34, k1_funct_1(C_35, A_34)), C_35) | ~r2_hidden(A_34, k1_relat_1(C_35)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.45  tff(c_12, plain, (![B_11, C_12, A_10]: (r2_hidden(B_11, k2_relat_1(C_12)) | ~r2_hidden(k4_tarski(A_10, B_11), C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.45  tff(c_72, plain, (![C_35, A_34]: (r2_hidden(k1_funct_1(C_35, A_34), k2_relat_1(C_35)) | ~r2_hidden(A_34, k1_relat_1(C_35)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_60, c_12])).
% 2.92/1.45  tff(c_16, plain, (![A_13, C_15]: (r2_hidden(k4_tarski(A_13, k1_funct_1(C_15, A_13)), C_15) | ~r2_hidden(A_13, k1_relat_1(C_15)) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.45  tff(c_88, plain, (![A_41, C_42, B_43, D_44]: (r2_hidden(A_41, k10_relat_1(C_42, B_43)) | ~r2_hidden(D_44, B_43) | ~r2_hidden(k4_tarski(A_41, D_44), C_42) | ~r2_hidden(D_44, k2_relat_1(C_42)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.45  tff(c_222, plain, (![A_58, C_59]: (r2_hidden(A_58, k10_relat_1(C_59, k1_relat_1('#skF_3'))) | ~r2_hidden(k4_tarski(A_58, k1_funct_1('#skF_4', '#skF_2')), C_59) | ~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k2_relat_1(C_59)) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_44, c_88])).
% 2.92/1.45  tff(c_234, plain, (r2_hidden('#skF_2', k10_relat_1('#skF_4', k1_relat_1('#skF_3'))) | ~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k2_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_222])).
% 2.92/1.45  tff(c_239, plain, (r2_hidden('#skF_2', k10_relat_1('#skF_4', k1_relat_1('#skF_3'))) | ~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_41, c_234])).
% 2.92/1.45  tff(c_240, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_239])).
% 2.92/1.45  tff(c_243, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_240])).
% 2.92/1.45  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_41, c_243])).
% 2.92/1.45  tff(c_248, plain, (r2_hidden('#skF_2', k10_relat_1('#skF_4', k1_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_239])).
% 2.92/1.45  tff(c_274, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_248])).
% 2.92/1.45  tff(c_283, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_274])).
% 2.92/1.45  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_283])).
% 2.92/1.45  tff(c_286, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 2.92/1.45  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_286])).
% 2.92/1.45  tff(c_290, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_36])).
% 2.92/1.45  tff(c_291, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_36])).
% 2.92/1.45  tff(c_306, plain, (![A_73, B_74, C_75]: (r2_hidden(k4_tarski(A_73, '#skF_1'(A_73, B_74, C_75)), C_75) | ~r2_hidden(A_73, k10_relat_1(C_75, B_74)) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.45  tff(c_18, plain, (![C_15, A_13, B_14]: (k1_funct_1(C_15, A_13)=B_14 | ~r2_hidden(k4_tarski(A_13, B_14), C_15) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.45  tff(c_353, plain, (![C_83, A_84, B_85]: (k1_funct_1(C_83, A_84)='#skF_1'(A_84, B_85, C_83) | ~v1_funct_1(C_83) | ~r2_hidden(A_84, k10_relat_1(C_83, B_85)) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_306, c_18])).
% 2.92/1.45  tff(c_533, plain, (![A_105, B_106, A_107]: ('#skF_1'(A_105, k1_relat_1(B_106), A_107)=k1_funct_1(A_107, A_105) | ~v1_funct_1(A_107) | ~r2_hidden(A_105, k1_relat_1(k5_relat_1(A_107, B_106))) | ~v1_relat_1(A_107) | ~v1_relat_1(B_106) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_10, c_353])).
% 2.92/1.45  tff(c_555, plain, ('#skF_1'('#skF_2', k1_relat_1('#skF_3'), '#skF_4')=k1_funct_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_290, c_533])).
% 2.92/1.45  tff(c_565, plain, ('#skF_1'('#skF_2', k1_relat_1('#skF_3'), '#skF_4')=k1_funct_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_22, c_555])).
% 2.92/1.45  tff(c_4, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | ~r2_hidden(A_1, k10_relat_1(C_3, B_2)) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.45  tff(c_575, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3')) | ~r2_hidden('#skF_2', k10_relat_1('#skF_4', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_565, c_4])).
% 2.92/1.45  tff(c_583, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k1_relat_1('#skF_3')) | ~r2_hidden('#skF_2', k10_relat_1('#skF_4', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_575])).
% 2.92/1.45  tff(c_584, plain, (~r2_hidden('#skF_2', k10_relat_1('#skF_4', k1_relat_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_291, c_583])).
% 2.92/1.45  tff(c_588, plain, (~r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_584])).
% 2.92/1.45  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_290, c_588])).
% 2.92/1.45  tff(c_593, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 2.92/1.45  tff(c_592, plain, (r2_hidden('#skF_2', k1_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_40])).
% 2.92/1.45  tff(c_609, plain, (![A_125, B_126, C_127]: (r2_hidden(k4_tarski(A_125, '#skF_1'(A_125, B_126, C_127)), C_127) | ~r2_hidden(A_125, k10_relat_1(C_127, B_126)) | ~v1_relat_1(C_127))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.92/1.45  tff(c_14, plain, (![A_10, C_12, B_11]: (r2_hidden(A_10, k1_relat_1(C_12)) | ~r2_hidden(k4_tarski(A_10, B_11), C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.45  tff(c_636, plain, (![A_130, C_131, B_132]: (r2_hidden(A_130, k1_relat_1(C_131)) | ~r2_hidden(A_130, k10_relat_1(C_131, B_132)) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_609, c_14])).
% 2.92/1.45  tff(c_696, plain, (![A_142, A_143, B_144]: (r2_hidden(A_142, k1_relat_1(A_143)) | ~r2_hidden(A_142, k1_relat_1(k5_relat_1(A_143, B_144))) | ~v1_relat_1(A_143) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_10, c_636])).
% 2.92/1.45  tff(c_711, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_592, c_696])).
% 2.92/1.45  tff(c_717, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_711])).
% 2.92/1.45  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_593, c_717])).
% 2.92/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.45  
% 2.92/1.45  Inference rules
% 2.92/1.45  ----------------------
% 2.92/1.45  #Ref     : 0
% 2.92/1.45  #Sup     : 139
% 2.92/1.45  #Fact    : 0
% 2.92/1.45  #Define  : 0
% 2.92/1.45  #Split   : 4
% 2.92/1.45  #Chain   : 0
% 2.92/1.45  #Close   : 0
% 2.92/1.45  
% 2.92/1.45  Ordering : KBO
% 2.92/1.45  
% 2.92/1.45  Simplification rules
% 2.92/1.45  ----------------------
% 2.92/1.45  #Subsume      : 12
% 2.92/1.45  #Demod        : 37
% 2.92/1.45  #Tautology    : 20
% 2.92/1.45  #SimpNegUnit  : 3
% 2.92/1.45  #BackRed      : 0
% 2.92/1.45  
% 2.92/1.45  #Partial instantiations: 0
% 2.92/1.45  #Strategies tried      : 1
% 2.92/1.45  
% 2.92/1.45  Timing (in seconds)
% 2.92/1.45  ----------------------
% 2.92/1.45  Preprocessing        : 0.30
% 2.92/1.45  Parsing              : 0.16
% 2.92/1.45  CNF conversion       : 0.02
% 2.92/1.45  Main loop            : 0.37
% 2.92/1.45  Inferencing          : 0.14
% 2.92/1.45  Reduction            : 0.10
% 2.92/1.45  Demodulation         : 0.07
% 2.92/1.45  BG Simplification    : 0.02
% 2.92/1.45  Subsumption          : 0.07
% 2.92/1.45  Abstraction          : 0.03
% 2.92/1.45  MUC search           : 0.00
% 2.92/1.45  Cooper               : 0.00
% 2.92/1.45  Total                : 0.70
% 2.92/1.45  Index Insertion      : 0.00
% 2.92/1.45  Index Deletion       : 0.00
% 2.92/1.45  Index Matching       : 0.00
% 2.92/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
