%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:21 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 142 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 238 expanded)
%              Number of equality atoms :   29 (  61 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ~ ( r2_hidden(A,k4_zfmisc_1(B,C,D,E))
          & ! [F,G,H,I] :
              ~ ( r2_hidden(F,B)
                & r2_hidden(G,C)
                & r2_hidden(H,D)
                & r2_hidden(I,E)
                & A = k4_mcart_1(F,G,H,I) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(c_20,plain,(
    r2_hidden('#skF_1',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_61,B_62,C_63,D_64] : k2_zfmisc_1(k3_zfmisc_1(A_61,B_62,C_63),D_64) = k4_zfmisc_1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [C_70,B_72,A_73,A_69,D_71] :
      ( r2_hidden(k2_mcart_1(A_69),D_71)
      | ~ r2_hidden(A_69,k4_zfmisc_1(A_73,B_72,C_70,D_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_12])).

tff(c_101,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_98])).

tff(c_2,plain,(
    ! [A_1,B_2] : v1_relat_1(k2_zfmisc_1(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_61,B_62,C_63,D_64] : v1_relat_1(k4_zfmisc_1(A_61,B_62,C_63,D_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_2])).

tff(c_62,plain,(
    ! [A_51,B_52] :
      ( k4_tarski(k1_mcart_1(A_51),k2_mcart_1(A_51)) = A_51
      | ~ r2_hidden(A_51,B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,
    ( k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_106,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_65])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_224,plain,(
    ! [A_98,D_96,C_95,B_97,A_94] :
      ( r2_hidden(k1_mcart_1(A_94),k3_zfmisc_1(A_98,B_97,C_95))
      | ~ r2_hidden(A_94,k4_zfmisc_1(A_98,B_97,C_95,D_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_14])).

tff(c_227,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_224])).

tff(c_38,plain,(
    ! [A_38,B_39,C_40] : k2_zfmisc_1(k2_zfmisc_1(A_38,B_39),C_40) = k3_zfmisc_1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_17,C_40,A_38,B_39] :
      ( r2_hidden(k2_mcart_1(A_17),C_40)
      | ~ r2_hidden(A_17,k3_zfmisc_1(A_38,B_39,C_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_238,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_227,c_46])).

tff(c_48,plain,(
    ! [A_38,B_39,C_40] : v1_relat_1(k3_zfmisc_1(A_38,B_39,C_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( k4_tarski(k1_mcart_1(A_20),k2_mcart_1(A_20)) = A_20
      | ~ r2_hidden(A_20,B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')),k2_mcart_1(k1_mcart_1('#skF_1'))) = k1_mcart_1('#skF_1')
    | ~ v1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_227,c_16])).

tff(c_237,plain,(
    k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')),k2_mcart_1(k1_mcart_1('#skF_1'))) = k1_mcart_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_231])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_tarski(k4_tarski(A_3,B_4),C_5) = k3_mcart_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_266,plain,(
    ! [C_5] : k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')),k2_mcart_1(k1_mcart_1('#skF_1')),C_5) = k4_tarski(k1_mcart_1('#skF_1'),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_4])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_zfmisc_1(k2_zfmisc_1(A_6,B_7),C_8) = k3_zfmisc_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k1_mcart_1(A_41),B_42)
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,(
    ! [A_41,A_6,B_7,C_8] :
      ( r2_hidden(k1_mcart_1(A_41),k2_zfmisc_1(A_6,B_7))
      | ~ r2_hidden(A_41,k3_zfmisc_1(A_6,B_7,C_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_234,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1')),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_227,c_59])).

tff(c_252,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_234,c_14])).

tff(c_253,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_234,c_12])).

tff(c_244,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')))) = k1_mcart_1(k1_mcart_1('#skF_1'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_234,c_16])).

tff(c_251,plain,(
    k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')))) = k1_mcart_1(k1_mcart_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_244])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k4_tarski(k3_mcart_1(A_9,B_10,C_11),D_12) = k4_mcart_1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_32,B_33,C_34] : k4_tarski(k4_tarski(A_32,B_33),C_34) = k3_mcart_1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    ! [A_32,B_33,C_34,C_5] : k3_mcart_1(k4_tarski(A_32,B_33),C_34,C_5) = k4_tarski(k3_mcart_1(A_32,B_33,C_34),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4])).

tff(c_168,plain,(
    ! [A_32,B_33,C_34,C_5] : k3_mcart_1(k4_tarski(A_32,B_33),C_34,C_5) = k4_mcart_1(A_32,B_33,C_34,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_25])).

tff(c_487,plain,(
    ! [C_135,C_136] : k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),C_135,C_136) = k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')),C_135,C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_168])).

tff(c_18,plain,(
    ! [F_26,G_27,H_28,I_29] :
      ( k4_mcart_1(F_26,G_27,H_28,I_29) != '#skF_1'
      | ~ r2_hidden(I_29,'#skF_5')
      | ~ r2_hidden(H_28,'#skF_4')
      | ~ r2_hidden(G_27,'#skF_3')
      | ~ r2_hidden(F_26,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_494,plain,(
    ! [C_135,C_136] :
      ( k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')),C_135,C_136) != '#skF_1'
      | ~ r2_hidden(C_136,'#skF_5')
      | ~ r2_hidden(C_135,'#skF_4')
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),'#skF_3')
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_18])).

tff(c_504,plain,(
    ! [C_137,C_138] :
      ( k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')),C_137,C_138) != '#skF_1'
      | ~ r2_hidden(C_138,'#skF_5')
      | ~ r2_hidden(C_137,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_253,c_494])).

tff(c_507,plain,(
    ! [C_5] :
      ( k4_tarski(k1_mcart_1('#skF_1'),C_5) != '#skF_1'
      | ~ r2_hidden(C_5,'#skF_5')
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_504])).

tff(c_510,plain,(
    ! [C_139] :
      ( k4_tarski(k1_mcart_1('#skF_1'),C_139) != '#skF_1'
      | ~ r2_hidden(C_139,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_507])).

tff(c_513,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_1'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_510])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.34  %$ r2_hidden > v1_relat_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.51/1.34  
% 2.51/1.34  %Foreground sorts:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Background operators:
% 2.51/1.34  
% 2.51/1.34  
% 2.51/1.34  %Foreground operators:
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.34  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.51/1.34  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.51/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.34  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.51/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.51/1.34  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.51/1.34  
% 2.51/1.36  tff(f_63, negated_conjecture, ~(![A, B, C, D, E]: ~(r2_hidden(A, k4_zfmisc_1(B, C, D, E)) & (![F, G, H, I]: ~((((r2_hidden(F, B) & r2_hidden(G, C)) & r2_hidden(H, D)) & r2_hidden(I, E)) & (A = k4_mcart_1(F, G, H, I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 2.51/1.36  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 2.51/1.36  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.51/1.36  tff(f_27, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.51/1.36  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.51/1.36  tff(f_31, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.51/1.36  tff(f_29, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.51/1.36  tff(f_33, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 2.51/1.36  tff(c_20, plain, (r2_hidden('#skF_1', k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.36  tff(c_79, plain, (![A_61, B_62, C_63, D_64]: (k2_zfmisc_1(k3_zfmisc_1(A_61, B_62, C_63), D_64)=k4_zfmisc_1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.36  tff(c_12, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.36  tff(c_98, plain, (![C_70, B_72, A_73, A_69, D_71]: (r2_hidden(k2_mcart_1(A_69), D_71) | ~r2_hidden(A_69, k4_zfmisc_1(A_73, B_72, C_70, D_71)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_12])).
% 2.51/1.36  tff(c_101, plain, (r2_hidden(k2_mcart_1('#skF_1'), '#skF_5')), inference(resolution, [status(thm)], [c_20, c_98])).
% 2.51/1.36  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.36  tff(c_91, plain, (![A_61, B_62, C_63, D_64]: (v1_relat_1(k4_zfmisc_1(A_61, B_62, C_63, D_64)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_2])).
% 2.51/1.36  tff(c_62, plain, (![A_51, B_52]: (k4_tarski(k1_mcart_1(A_51), k2_mcart_1(A_51))=A_51 | ~r2_hidden(A_51, B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.36  tff(c_65, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1' | ~v1_relat_1(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_62])).
% 2.51/1.36  tff(c_106, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_65])).
% 2.51/1.36  tff(c_14, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.36  tff(c_224, plain, (![A_98, D_96, C_95, B_97, A_94]: (r2_hidden(k1_mcart_1(A_94), k3_zfmisc_1(A_98, B_97, C_95)) | ~r2_hidden(A_94, k4_zfmisc_1(A_98, B_97, C_95, D_96)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_14])).
% 2.51/1.36  tff(c_227, plain, (r2_hidden(k1_mcart_1('#skF_1'), k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_224])).
% 2.51/1.36  tff(c_38, plain, (![A_38, B_39, C_40]: (k2_zfmisc_1(k2_zfmisc_1(A_38, B_39), C_40)=k3_zfmisc_1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.36  tff(c_46, plain, (![A_17, C_40, A_38, B_39]: (r2_hidden(k2_mcart_1(A_17), C_40) | ~r2_hidden(A_17, k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_12])).
% 2.51/1.36  tff(c_238, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')), '#skF_4')), inference(resolution, [status(thm)], [c_227, c_46])).
% 2.51/1.36  tff(c_48, plain, (![A_38, B_39, C_40]: (v1_relat_1(k3_zfmisc_1(A_38, B_39, C_40)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2])).
% 2.51/1.36  tff(c_16, plain, (![A_20, B_21]: (k4_tarski(k1_mcart_1(A_20), k2_mcart_1(A_20))=A_20 | ~r2_hidden(A_20, B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.36  tff(c_231, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')), k2_mcart_1(k1_mcart_1('#skF_1')))=k1_mcart_1('#skF_1') | ~v1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_227, c_16])).
% 2.51/1.36  tff(c_237, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_1')), k2_mcart_1(k1_mcart_1('#skF_1')))=k1_mcart_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_231])).
% 2.51/1.36  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_tarski(k4_tarski(A_3, B_4), C_5)=k3_mcart_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.36  tff(c_266, plain, (![C_5]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')), k2_mcart_1(k1_mcart_1('#skF_1')), C_5)=k4_tarski(k1_mcart_1('#skF_1'), C_5))), inference(superposition, [status(thm), theory('equality')], [c_237, c_4])).
% 2.51/1.36  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_zfmisc_1(k2_zfmisc_1(A_6, B_7), C_8)=k3_zfmisc_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.36  tff(c_57, plain, (![A_41, B_42, C_43]: (r2_hidden(k1_mcart_1(A_41), B_42) | ~r2_hidden(A_41, k2_zfmisc_1(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.36  tff(c_59, plain, (![A_41, A_6, B_7, C_8]: (r2_hidden(k1_mcart_1(A_41), k2_zfmisc_1(A_6, B_7)) | ~r2_hidden(A_41, k3_zfmisc_1(A_6, B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_57])).
% 2.51/1.36  tff(c_234, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_1')), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_227, c_59])).
% 2.51/1.36  tff(c_252, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), '#skF_2')), inference(resolution, [status(thm)], [c_234, c_14])).
% 2.51/1.36  tff(c_253, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), '#skF_3')), inference(resolution, [status(thm)], [c_234, c_12])).
% 2.51/1.36  tff(c_244, plain, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))))=k1_mcart_1(k1_mcart_1('#skF_1')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_234, c_16])).
% 2.51/1.36  tff(c_251, plain, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))))=k1_mcart_1(k1_mcart_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_244])).
% 2.51/1.36  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k4_tarski(k3_mcart_1(A_9, B_10, C_11), D_12)=k4_mcart_1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.36  tff(c_22, plain, (![A_32, B_33, C_34]: (k4_tarski(k4_tarski(A_32, B_33), C_34)=k3_mcart_1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.36  tff(c_25, plain, (![A_32, B_33, C_34, C_5]: (k3_mcart_1(k4_tarski(A_32, B_33), C_34, C_5)=k4_tarski(k3_mcart_1(A_32, B_33, C_34), C_5))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4])).
% 2.51/1.36  tff(c_168, plain, (![A_32, B_33, C_34, C_5]: (k3_mcart_1(k4_tarski(A_32, B_33), C_34, C_5)=k4_mcart_1(A_32, B_33, C_34, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_25])).
% 2.51/1.36  tff(c_487, plain, (![C_135, C_136]: (k4_mcart_1(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), C_135, C_136)=k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')), C_135, C_136))), inference(superposition, [status(thm), theory('equality')], [c_251, c_168])).
% 2.51/1.36  tff(c_18, plain, (![F_26, G_27, H_28, I_29]: (k4_mcart_1(F_26, G_27, H_28, I_29)!='#skF_1' | ~r2_hidden(I_29, '#skF_5') | ~r2_hidden(H_28, '#skF_4') | ~r2_hidden(G_27, '#skF_3') | ~r2_hidden(F_26, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.36  tff(c_494, plain, (![C_135, C_136]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')), C_135, C_136)!='#skF_1' | ~r2_hidden(C_136, '#skF_5') | ~r2_hidden(C_135, '#skF_4') | ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), '#skF_3') | ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1'))), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_18])).
% 2.51/1.36  tff(c_504, plain, (![C_137, C_138]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_1')), C_137, C_138)!='#skF_1' | ~r2_hidden(C_138, '#skF_5') | ~r2_hidden(C_137, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_253, c_494])).
% 2.51/1.36  tff(c_507, plain, (![C_5]: (k4_tarski(k1_mcart_1('#skF_1'), C_5)!='#skF_1' | ~r2_hidden(C_5, '#skF_5') | ~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_1')), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_504])).
% 2.51/1.36  tff(c_510, plain, (![C_139]: (k4_tarski(k1_mcart_1('#skF_1'), C_139)!='#skF_1' | ~r2_hidden(C_139, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_507])).
% 2.51/1.36  tff(c_513, plain, (~r2_hidden(k2_mcart_1('#skF_1'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_106, c_510])).
% 2.51/1.36  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_513])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 131
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 4
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 12
% 2.51/1.36  #Demod        : 84
% 2.51/1.36  #Tautology    : 67
% 2.51/1.36  #SimpNegUnit  : 0
% 2.51/1.36  #BackRed      : 0
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.36  Preprocessing        : 0.25
% 2.51/1.36  Parsing              : 0.13
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.32
% 2.51/1.36  Inferencing          : 0.14
% 2.51/1.36  Reduction            : 0.10
% 2.51/1.36  Demodulation         : 0.08
% 2.51/1.36  BG Simplification    : 0.02
% 2.51/1.36  Subsumption          : 0.05
% 2.51/1.36  Abstraction          : 0.02
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.60
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.36  Index Deletion       : 0.00
% 2.51/1.36  Index Matching       : 0.00
% 2.51/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
