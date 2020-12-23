%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 102 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 251 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_6 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> ! [B,C,D] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,D),A) )
           => r2_hidden(k4_tarski(B,D),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : v8_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

tff(c_34,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28])).

tff(c_68,plain,(
    ! [A_38] :
      ( r2_hidden(k4_tarski('#skF_2'(A_38),'#skF_3'(A_38)),A_38)
      | v8_relat_2(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [B_5,C_6,A_4] :
      ( r2_hidden(B_5,k3_relat_1(C_6))
      | ~ r2_hidden(k4_tarski(A_4,B_5),C_6)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_3'(A_39),k3_relat_1(A_39))
      | v8_relat_2(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_76,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_17)),A_17)
      | v8_relat_2(k1_wellord2(A_17))
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_73])).

tff(c_78,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_17)),A_17)
      | v8_relat_2(k1_wellord2(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_14,plain,(
    ! [A_7] :
      ( r2_hidden(k4_tarski('#skF_1'(A_7),'#skF_2'(A_7)),A_7)
      | v8_relat_2(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(A_41,k3_relat_1(C_42))
      | ~ r2_hidden(k4_tarski(A_41,B_43),C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_1'(A_44),k3_relat_1(A_44))
      | v8_relat_2(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_92,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_17)),A_17)
      | v8_relat_2(k1_wellord2(A_17))
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_89])).

tff(c_94,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_1'(k1_wellord2(A_17)),A_17)
      | v8_relat_2(k1_wellord2(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_92])).

tff(c_55,plain,(
    ! [A_34] :
      ( r2_hidden(k4_tarski('#skF_1'(A_34),'#skF_2'(A_34)),A_34)
      | v8_relat_2(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_2'(A_35),k3_relat_1(A_35))
      | v8_relat_2(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_63,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_17)),A_17)
      | v8_relat_2(k1_wellord2(A_17))
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_65,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(k1_wellord2(A_17)),A_17)
      | v8_relat_2(k1_wellord2(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_63])).

tff(c_32,plain,(
    ! [C_23,D_24,A_17] :
      ( r1_tarski(C_23,D_24)
      | ~ r2_hidden(k4_tarski(C_23,D_24),k1_wellord2(A_17))
      | ~ r2_hidden(D_24,A_17)
      | ~ r2_hidden(C_23,A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    ! [C_51,D_52,A_53] :
      ( r1_tarski(C_51,D_52)
      | ~ r2_hidden(k4_tarski(C_51,D_52),k1_wellord2(A_53))
      | ~ r2_hidden(D_52,A_53)
      | ~ r2_hidden(C_51,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_149,plain,(
    ! [A_53] :
      ( r1_tarski('#skF_1'(k1_wellord2(A_53)),'#skF_2'(k1_wellord2(A_53)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_53)),A_53)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_53)),A_53)
      | v8_relat_2(k1_wellord2(A_53))
      | ~ v1_relat_1(k1_wellord2(A_53)) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_156,plain,(
    ! [A_53] :
      ( r1_tarski('#skF_1'(k1_wellord2(A_53)),'#skF_2'(k1_wellord2(A_53)))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_53)),A_53)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_53)),A_53)
      | v8_relat_2(k1_wellord2(A_53)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_149])).

tff(c_12,plain,(
    ! [A_7] :
      ( r2_hidden(k4_tarski('#skF_2'(A_7),'#skF_3'(A_7)),A_7)
      | v8_relat_2(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    ! [A_53] :
      ( r1_tarski('#skF_2'(k1_wellord2(A_53)),'#skF_3'(k1_wellord2(A_53)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_53)),A_53)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_53)),A_53)
      | v8_relat_2(k1_wellord2(A_53))
      | ~ v1_relat_1(k1_wellord2(A_53)) ) ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_173,plain,(
    ! [A_59] :
      ( r1_tarski('#skF_2'(k1_wellord2(A_59)),'#skF_3'(k1_wellord2(A_59)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_59)),A_59)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_59)),A_59)
      | v8_relat_2(k1_wellord2(A_59)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_145])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [A_61,A_62] :
      ( r1_tarski(A_61,'#skF_3'(k1_wellord2(A_62)))
      | ~ r1_tarski(A_61,'#skF_2'(k1_wellord2(A_62)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_62)),A_62)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_62)),A_62)
      | v8_relat_2(k1_wellord2(A_62)) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_354,plain,(
    ! [A_93] :
      ( r1_tarski('#skF_1'(k1_wellord2(A_93)),'#skF_3'(k1_wellord2(A_93)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_93)),A_93)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_93)),A_93)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_93)),A_93)
      | v8_relat_2(k1_wellord2(A_93)) ) ),
    inference(resolution,[status(thm)],[c_156,c_178])).

tff(c_30,plain,(
    ! [C_23,D_24,A_17] :
      ( r2_hidden(k4_tarski(C_23,D_24),k1_wellord2(A_17))
      | ~ r1_tarski(C_23,D_24)
      | ~ r2_hidden(D_24,A_17)
      | ~ r2_hidden(C_23,A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_118,plain,(
    ! [C_48,D_49,A_50] :
      ( r2_hidden(k4_tarski(C_48,D_49),k1_wellord2(A_50))
      | ~ r1_tarski(C_48,D_49)
      | ~ r2_hidden(D_49,A_50)
      | ~ r2_hidden(C_48,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_10,plain,(
    ! [A_7] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_7),'#skF_3'(A_7)),A_7)
      | v8_relat_2(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [A_50] :
      ( v8_relat_2(k1_wellord2(A_50))
      | ~ v1_relat_1(k1_wellord2(A_50))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_50)),'#skF_3'(k1_wellord2(A_50)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_50)),A_50)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_50)),A_50) ) ),
    inference(resolution,[status(thm)],[c_118,c_10])).

tff(c_134,plain,(
    ! [A_50] :
      ( v8_relat_2(k1_wellord2(A_50))
      | ~ r1_tarski('#skF_1'(k1_wellord2(A_50)),'#skF_3'(k1_wellord2(A_50)))
      | ~ r2_hidden('#skF_3'(k1_wellord2(A_50)),A_50)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_50)),A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_125])).

tff(c_368,plain,(
    ! [A_94] :
      ( ~ r2_hidden('#skF_3'(k1_wellord2(A_94)),A_94)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_94)),A_94)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_94)),A_94)
      | v8_relat_2(k1_wellord2(A_94)) ) ),
    inference(resolution,[status(thm)],[c_354,c_134])).

tff(c_422,plain,(
    ! [A_98] :
      ( ~ r2_hidden('#skF_3'(k1_wellord2(A_98)),A_98)
      | ~ r2_hidden('#skF_1'(k1_wellord2(A_98)),A_98)
      | v8_relat_2(k1_wellord2(A_98)) ) ),
    inference(resolution,[status(thm)],[c_65,c_368])).

tff(c_427,plain,(
    ! [A_99] :
      ( ~ r2_hidden('#skF_3'(k1_wellord2(A_99)),A_99)
      | v8_relat_2(k1_wellord2(A_99)) ) ),
    inference(resolution,[status(thm)],[c_94,c_422])).

tff(c_431,plain,(
    ! [A_17] : v8_relat_2(k1_wellord2(A_17)) ),
    inference(resolution,[status(thm)],[c_78,c_427])).

tff(c_36,plain,(
    ~ v8_relat_2(k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.36  
% 2.58/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.36  %$ r2_hidden > r1_tarski > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_2 > #skF_1 > #skF_6 > #skF_3 > #skF_5 > #skF_4
% 2.58/1.36  
% 2.58/1.36  %Foreground sorts:
% 2.58/1.36  
% 2.58/1.36  
% 2.58/1.36  %Background operators:
% 2.58/1.36  
% 2.58/1.36  
% 2.58/1.36  %Foreground operators:
% 2.58/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.58/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.58/1.36  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.58/1.36  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.58/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.36  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.58/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.58/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.36  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.58/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.58/1.36  
% 2.58/1.38  tff(f_67, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.58/1.38  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.58/1.38  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> (![B, C, D]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, D), A)) => r2_hidden(k4_tarski(B, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_wellord1)).
% 2.58/1.38  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 2.58/1.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.58/1.38  tff(f_70, negated_conjecture, ~(![A]: v8_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_wellord2)).
% 2.58/1.38  tff(c_34, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.38  tff(c_28, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.58/1.38  tff(c_42, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28])).
% 2.58/1.38  tff(c_68, plain, (![A_38]: (r2_hidden(k4_tarski('#skF_2'(A_38), '#skF_3'(A_38)), A_38) | v8_relat_2(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.38  tff(c_4, plain, (![B_5, C_6, A_4]: (r2_hidden(B_5, k3_relat_1(C_6)) | ~r2_hidden(k4_tarski(A_4, B_5), C_6) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.38  tff(c_73, plain, (![A_39]: (r2_hidden('#skF_3'(A_39), k3_relat_1(A_39)) | v8_relat_2(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_68, c_4])).
% 2.58/1.38  tff(c_76, plain, (![A_17]: (r2_hidden('#skF_3'(k1_wellord2(A_17)), A_17) | v8_relat_2(k1_wellord2(A_17)) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_73])).
% 2.58/1.38  tff(c_78, plain, (![A_17]: (r2_hidden('#skF_3'(k1_wellord2(A_17)), A_17) | v8_relat_2(k1_wellord2(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 2.58/1.38  tff(c_14, plain, (![A_7]: (r2_hidden(k4_tarski('#skF_1'(A_7), '#skF_2'(A_7)), A_7) | v8_relat_2(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.38  tff(c_80, plain, (![A_41, C_42, B_43]: (r2_hidden(A_41, k3_relat_1(C_42)) | ~r2_hidden(k4_tarski(A_41, B_43), C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.38  tff(c_89, plain, (![A_44]: (r2_hidden('#skF_1'(A_44), k3_relat_1(A_44)) | v8_relat_2(A_44) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_14, c_80])).
% 2.58/1.38  tff(c_92, plain, (![A_17]: (r2_hidden('#skF_1'(k1_wellord2(A_17)), A_17) | v8_relat_2(k1_wellord2(A_17)) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_89])).
% 2.58/1.38  tff(c_94, plain, (![A_17]: (r2_hidden('#skF_1'(k1_wellord2(A_17)), A_17) | v8_relat_2(k1_wellord2(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_92])).
% 2.58/1.38  tff(c_55, plain, (![A_34]: (r2_hidden(k4_tarski('#skF_1'(A_34), '#skF_2'(A_34)), A_34) | v8_relat_2(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.38  tff(c_60, plain, (![A_35]: (r2_hidden('#skF_2'(A_35), k3_relat_1(A_35)) | v8_relat_2(A_35) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_55, c_4])).
% 2.58/1.38  tff(c_63, plain, (![A_17]: (r2_hidden('#skF_2'(k1_wellord2(A_17)), A_17) | v8_relat_2(k1_wellord2(A_17)) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_60])).
% 2.58/1.38  tff(c_65, plain, (![A_17]: (r2_hidden('#skF_2'(k1_wellord2(A_17)), A_17) | v8_relat_2(k1_wellord2(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_63])).
% 2.58/1.38  tff(c_32, plain, (![C_23, D_24, A_17]: (r1_tarski(C_23, D_24) | ~r2_hidden(k4_tarski(C_23, D_24), k1_wellord2(A_17)) | ~r2_hidden(D_24, A_17) | ~r2_hidden(C_23, A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.58/1.38  tff(c_138, plain, (![C_51, D_52, A_53]: (r1_tarski(C_51, D_52) | ~r2_hidden(k4_tarski(C_51, D_52), k1_wellord2(A_53)) | ~r2_hidden(D_52, A_53) | ~r2_hidden(C_51, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 2.58/1.38  tff(c_149, plain, (![A_53]: (r1_tarski('#skF_1'(k1_wellord2(A_53)), '#skF_2'(k1_wellord2(A_53))) | ~r2_hidden('#skF_2'(k1_wellord2(A_53)), A_53) | ~r2_hidden('#skF_1'(k1_wellord2(A_53)), A_53) | v8_relat_2(k1_wellord2(A_53)) | ~v1_relat_1(k1_wellord2(A_53)))), inference(resolution, [status(thm)], [c_14, c_138])).
% 2.58/1.38  tff(c_156, plain, (![A_53]: (r1_tarski('#skF_1'(k1_wellord2(A_53)), '#skF_2'(k1_wellord2(A_53))) | ~r2_hidden('#skF_2'(k1_wellord2(A_53)), A_53) | ~r2_hidden('#skF_1'(k1_wellord2(A_53)), A_53) | v8_relat_2(k1_wellord2(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_149])).
% 2.58/1.38  tff(c_12, plain, (![A_7]: (r2_hidden(k4_tarski('#skF_2'(A_7), '#skF_3'(A_7)), A_7) | v8_relat_2(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.38  tff(c_145, plain, (![A_53]: (r1_tarski('#skF_2'(k1_wellord2(A_53)), '#skF_3'(k1_wellord2(A_53))) | ~r2_hidden('#skF_3'(k1_wellord2(A_53)), A_53) | ~r2_hidden('#skF_2'(k1_wellord2(A_53)), A_53) | v8_relat_2(k1_wellord2(A_53)) | ~v1_relat_1(k1_wellord2(A_53)))), inference(resolution, [status(thm)], [c_12, c_138])).
% 2.58/1.38  tff(c_173, plain, (![A_59]: (r1_tarski('#skF_2'(k1_wellord2(A_59)), '#skF_3'(k1_wellord2(A_59))) | ~r2_hidden('#skF_3'(k1_wellord2(A_59)), A_59) | ~r2_hidden('#skF_2'(k1_wellord2(A_59)), A_59) | v8_relat_2(k1_wellord2(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_145])).
% 2.58/1.38  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.38  tff(c_178, plain, (![A_61, A_62]: (r1_tarski(A_61, '#skF_3'(k1_wellord2(A_62))) | ~r1_tarski(A_61, '#skF_2'(k1_wellord2(A_62))) | ~r2_hidden('#skF_3'(k1_wellord2(A_62)), A_62) | ~r2_hidden('#skF_2'(k1_wellord2(A_62)), A_62) | v8_relat_2(k1_wellord2(A_62)))), inference(resolution, [status(thm)], [c_173, c_2])).
% 2.58/1.38  tff(c_354, plain, (![A_93]: (r1_tarski('#skF_1'(k1_wellord2(A_93)), '#skF_3'(k1_wellord2(A_93))) | ~r2_hidden('#skF_3'(k1_wellord2(A_93)), A_93) | ~r2_hidden('#skF_2'(k1_wellord2(A_93)), A_93) | ~r2_hidden('#skF_1'(k1_wellord2(A_93)), A_93) | v8_relat_2(k1_wellord2(A_93)))), inference(resolution, [status(thm)], [c_156, c_178])).
% 2.58/1.38  tff(c_30, plain, (![C_23, D_24, A_17]: (r2_hidden(k4_tarski(C_23, D_24), k1_wellord2(A_17)) | ~r1_tarski(C_23, D_24) | ~r2_hidden(D_24, A_17) | ~r2_hidden(C_23, A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.58/1.38  tff(c_118, plain, (![C_48, D_49, A_50]: (r2_hidden(k4_tarski(C_48, D_49), k1_wellord2(A_50)) | ~r1_tarski(C_48, D_49) | ~r2_hidden(D_49, A_50) | ~r2_hidden(C_48, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 2.58/1.38  tff(c_10, plain, (![A_7]: (~r2_hidden(k4_tarski('#skF_1'(A_7), '#skF_3'(A_7)), A_7) | v8_relat_2(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.38  tff(c_125, plain, (![A_50]: (v8_relat_2(k1_wellord2(A_50)) | ~v1_relat_1(k1_wellord2(A_50)) | ~r1_tarski('#skF_1'(k1_wellord2(A_50)), '#skF_3'(k1_wellord2(A_50))) | ~r2_hidden('#skF_3'(k1_wellord2(A_50)), A_50) | ~r2_hidden('#skF_1'(k1_wellord2(A_50)), A_50))), inference(resolution, [status(thm)], [c_118, c_10])).
% 2.58/1.38  tff(c_134, plain, (![A_50]: (v8_relat_2(k1_wellord2(A_50)) | ~r1_tarski('#skF_1'(k1_wellord2(A_50)), '#skF_3'(k1_wellord2(A_50))) | ~r2_hidden('#skF_3'(k1_wellord2(A_50)), A_50) | ~r2_hidden('#skF_1'(k1_wellord2(A_50)), A_50))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_125])).
% 2.58/1.38  tff(c_368, plain, (![A_94]: (~r2_hidden('#skF_3'(k1_wellord2(A_94)), A_94) | ~r2_hidden('#skF_2'(k1_wellord2(A_94)), A_94) | ~r2_hidden('#skF_1'(k1_wellord2(A_94)), A_94) | v8_relat_2(k1_wellord2(A_94)))), inference(resolution, [status(thm)], [c_354, c_134])).
% 2.58/1.38  tff(c_422, plain, (![A_98]: (~r2_hidden('#skF_3'(k1_wellord2(A_98)), A_98) | ~r2_hidden('#skF_1'(k1_wellord2(A_98)), A_98) | v8_relat_2(k1_wellord2(A_98)))), inference(resolution, [status(thm)], [c_65, c_368])).
% 2.58/1.38  tff(c_427, plain, (![A_99]: (~r2_hidden('#skF_3'(k1_wellord2(A_99)), A_99) | v8_relat_2(k1_wellord2(A_99)))), inference(resolution, [status(thm)], [c_94, c_422])).
% 2.58/1.38  tff(c_431, plain, (![A_17]: (v8_relat_2(k1_wellord2(A_17)))), inference(resolution, [status(thm)], [c_78, c_427])).
% 2.58/1.38  tff(c_36, plain, (~v8_relat_2(k1_wellord2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.58/1.38  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_431, c_36])).
% 2.58/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  Inference rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Ref     : 0
% 2.58/1.38  #Sup     : 81
% 2.58/1.38  #Fact    : 0
% 2.58/1.38  #Define  : 0
% 2.58/1.38  #Split   : 0
% 2.58/1.38  #Chain   : 0
% 2.58/1.38  #Close   : 0
% 2.58/1.38  
% 2.58/1.38  Ordering : KBO
% 2.58/1.38  
% 2.58/1.38  Simplification rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Subsume      : 19
% 2.58/1.38  #Demod        : 133
% 2.58/1.38  #Tautology    : 42
% 2.58/1.38  #SimpNegUnit  : 0
% 2.58/1.38  #BackRed      : 3
% 2.58/1.38  
% 2.58/1.38  #Partial instantiations: 0
% 2.58/1.38  #Strategies tried      : 1
% 2.58/1.38  
% 2.58/1.38  Timing (in seconds)
% 2.58/1.38  ----------------------
% 2.58/1.38  Preprocessing        : 0.30
% 2.58/1.38  Parsing              : 0.16
% 2.58/1.38  CNF conversion       : 0.02
% 2.58/1.38  Main loop            : 0.32
% 2.58/1.38  Inferencing          : 0.13
% 2.58/1.38  Reduction            : 0.09
% 2.58/1.38  Demodulation         : 0.06
% 2.58/1.38  BG Simplification    : 0.02
% 2.58/1.38  Subsumption          : 0.07
% 2.58/1.38  Abstraction          : 0.01
% 2.58/1.38  MUC search           : 0.00
% 2.58/1.38  Cooper               : 0.00
% 2.58/1.38  Total                : 0.65
% 2.58/1.38  Index Insertion      : 0.00
% 2.58/1.38  Index Deletion       : 0.00
% 2.58/1.38  Index Matching       : 0.00
% 2.58/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
