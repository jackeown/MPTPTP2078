%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:42 EST 2020

% Result     : Theorem 9.92s
% Output     : CNFRefutation 9.92s
% Verified   : 
% Statistics : Number of formulae       :   69 (  90 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 117 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_32,B_33] : r1_xboole_0(k4_xboole_0(A_32,B_33),B_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_351,plain,(
    ! [B_60,A_61] :
      ( k7_relat_1(B_60,A_61) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_362,plain,(
    ! [B_62] :
      ( k7_relat_1(B_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_59,c_351])).

tff(c_366,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_362])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_xboole_0(k4_xboole_0(A_10,B_11),B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_10,B_11] : k3_xboole_0(k4_xboole_0(A_10,B_11),B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_104])).

tff(c_18,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_137,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    ! [B_47,A_48] : k1_setfam_1(k2_tarski(B_47,A_48)) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_137])).

tff(c_22,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_200,plain,(
    ! [B_52,A_53] : k3_xboole_0(B_52,A_53) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_22])).

tff(c_252,plain,(
    ! [B_11,A_10] : k3_xboole_0(B_11,k4_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_200])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_304,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_xboole_0(A_55,C_56)
      | ~ r1_xboole_0(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_888,plain,(
    ! [A_105,B_106,A_107] :
      ( r1_xboole_0(A_105,B_106)
      | ~ r1_tarski(A_105,A_107)
      | k3_xboole_0(A_107,B_106) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_895,plain,(
    ! [B_108] :
      ( r1_xboole_0('#skF_1',B_108)
      | k3_xboole_0('#skF_2',B_108) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_888])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_903,plain,(
    ! [B_109] :
      ( k3_xboole_0('#skF_1',B_109) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_109) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_895,c_2])).

tff(c_925,plain,(
    ! [A_10] : k3_xboole_0('#skF_1',k4_xboole_0(A_10,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_903])).

tff(c_158,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_22])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [C_25,A_23,B_24] :
      ( k7_relat_1(C_25,k6_subset_1(A_23,B_24)) = k6_subset_1(C_25,k7_relat_1(C_25,B_24))
      | ~ r1_tarski(k1_relat_1(C_25),A_23)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_646,plain,(
    ! [C_86,A_87,B_88] :
      ( k7_relat_1(C_86,k4_xboole_0(A_87,B_88)) = k4_xboole_0(C_86,k7_relat_1(C_86,B_88))
      | ~ r1_tarski(k1_relat_1(C_86),A_87)
      | ~ v1_relat_1(C_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_26])).

tff(c_1879,plain,(
    ! [C_165,B_166,B_167] :
      ( k7_relat_1(C_165,k4_xboole_0(k2_xboole_0(k1_relat_1(C_165),B_166),B_167)) = k4_xboole_0(C_165,k7_relat_1(C_165,B_167))
      | ~ v1_relat_1(C_165) ) ),
    inference(resolution,[status(thm)],[c_16,c_646])).

tff(c_24,plain,(
    ! [C_22,A_20,B_21] :
      ( k7_relat_1(k7_relat_1(C_22,A_20),B_21) = k7_relat_1(C_22,k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3570,plain,(
    ! [C_247,B_248,B_249,B_250] :
      ( k7_relat_1(C_247,k3_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_247),B_248),B_249),B_250)) = k7_relat_1(k4_xboole_0(C_247,k7_relat_1(C_247,B_249)),B_250)
      | ~ v1_relat_1(C_247)
      | ~ v1_relat_1(C_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1879,c_24])).

tff(c_13119,plain,(
    ! [C_650,A_651,B_652,B_653] :
      ( k7_relat_1(C_650,k3_xboole_0(A_651,k4_xboole_0(k2_xboole_0(k1_relat_1(C_650),B_652),B_653))) = k7_relat_1(k4_xboole_0(C_650,k7_relat_1(C_650,B_653)),A_651)
      | ~ v1_relat_1(C_650)
      | ~ v1_relat_1(C_650) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_3570])).

tff(c_13409,plain,(
    ! [C_654] :
      ( k7_relat_1(k4_xboole_0(C_654,k7_relat_1(C_654,'#skF_2')),'#skF_1') = k7_relat_1(C_654,k1_xboole_0)
      | ~ v1_relat_1(C_654)
      | ~ v1_relat_1(C_654) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_13119])).

tff(c_32,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_37,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_13462,plain,
    ( k7_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13409,c_37])).

tff(c_13520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_366,c_13462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.92/3.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.66  
% 9.92/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.66  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.92/3.66  
% 9.92/3.66  %Foreground sorts:
% 9.92/3.66  
% 9.92/3.66  
% 9.92/3.66  %Background operators:
% 9.92/3.66  
% 9.92/3.66  
% 9.92/3.66  %Foreground operators:
% 9.92/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.92/3.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.92/3.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.92/3.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.92/3.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.92/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.92/3.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.92/3.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.92/3.66  tff('#skF_2', type, '#skF_2': $i).
% 9.92/3.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.92/3.66  tff('#skF_3', type, '#skF_3': $i).
% 9.92/3.66  tff('#skF_1', type, '#skF_1': $i).
% 9.92/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.92/3.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.92/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.92/3.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.92/3.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.92/3.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.92/3.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.92/3.66  
% 9.92/3.67  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 9.92/3.67  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.92/3.67  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.92/3.67  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 9.92/3.67  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.92/3.67  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.92/3.67  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.92/3.67  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 9.92/3.67  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.92/3.67  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.92/3.67  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 9.92/3.67  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 9.92/3.67  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.92/3.67  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.92/3.67  tff(c_56, plain, (![A_32, B_33]: (r1_xboole_0(k4_xboole_0(A_32, B_33), B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.92/3.67  tff(c_59, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_56])).
% 9.92/3.67  tff(c_351, plain, (![B_60, A_61]: (k7_relat_1(B_60, A_61)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.92/3.67  tff(c_362, plain, (![B_62]: (k7_relat_1(B_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_59, c_351])).
% 9.92/3.67  tff(c_366, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_362])).
% 9.92/3.67  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(k4_xboole_0(A_10, B_11), B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.92/3.67  tff(c_104, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.92/3.67  tff(c_117, plain, (![A_10, B_11]: (k3_xboole_0(k4_xboole_0(A_10, B_11), B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_104])).
% 9.92/3.67  tff(c_18, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.92/3.67  tff(c_137, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.92/3.67  tff(c_152, plain, (![B_47, A_48]: (k1_setfam_1(k2_tarski(B_47, A_48))=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_18, c_137])).
% 9.92/3.67  tff(c_22, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.92/3.67  tff(c_200, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_152, c_22])).
% 9.92/3.67  tff(c_252, plain, (![B_11, A_10]: (k3_xboole_0(B_11, k4_xboole_0(A_10, B_11))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117, c_200])).
% 9.92/3.67  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.92/3.67  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.92/3.67  tff(c_304, plain, (![A_55, C_56, B_57]: (r1_xboole_0(A_55, C_56) | ~r1_xboole_0(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.92/3.67  tff(c_888, plain, (![A_105, B_106, A_107]: (r1_xboole_0(A_105, B_106) | ~r1_tarski(A_105, A_107) | k3_xboole_0(A_107, B_106)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_304])).
% 9.92/3.67  tff(c_895, plain, (![B_108]: (r1_xboole_0('#skF_1', B_108) | k3_xboole_0('#skF_2', B_108)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_888])).
% 9.92/3.67  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.92/3.67  tff(c_903, plain, (![B_109]: (k3_xboole_0('#skF_1', B_109)=k1_xboole_0 | k3_xboole_0('#skF_2', B_109)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_895, c_2])).
% 9.92/3.67  tff(c_925, plain, (![A_10]: (k3_xboole_0('#skF_1', k4_xboole_0(A_10, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_252, c_903])).
% 9.92/3.67  tff(c_158, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_152, c_22])).
% 9.92/3.67  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.92/3.67  tff(c_20, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.92/3.67  tff(c_26, plain, (![C_25, A_23, B_24]: (k7_relat_1(C_25, k6_subset_1(A_23, B_24))=k6_subset_1(C_25, k7_relat_1(C_25, B_24)) | ~r1_tarski(k1_relat_1(C_25), A_23) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.92/3.67  tff(c_646, plain, (![C_86, A_87, B_88]: (k7_relat_1(C_86, k4_xboole_0(A_87, B_88))=k4_xboole_0(C_86, k7_relat_1(C_86, B_88)) | ~r1_tarski(k1_relat_1(C_86), A_87) | ~v1_relat_1(C_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_26])).
% 9.92/3.67  tff(c_1879, plain, (![C_165, B_166, B_167]: (k7_relat_1(C_165, k4_xboole_0(k2_xboole_0(k1_relat_1(C_165), B_166), B_167))=k4_xboole_0(C_165, k7_relat_1(C_165, B_167)) | ~v1_relat_1(C_165))), inference(resolution, [status(thm)], [c_16, c_646])).
% 9.92/3.67  tff(c_24, plain, (![C_22, A_20, B_21]: (k7_relat_1(k7_relat_1(C_22, A_20), B_21)=k7_relat_1(C_22, k3_xboole_0(A_20, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.92/3.67  tff(c_3570, plain, (![C_247, B_248, B_249, B_250]: (k7_relat_1(C_247, k3_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_247), B_248), B_249), B_250))=k7_relat_1(k4_xboole_0(C_247, k7_relat_1(C_247, B_249)), B_250) | ~v1_relat_1(C_247) | ~v1_relat_1(C_247))), inference(superposition, [status(thm), theory('equality')], [c_1879, c_24])).
% 9.92/3.67  tff(c_13119, plain, (![C_650, A_651, B_652, B_653]: (k7_relat_1(C_650, k3_xboole_0(A_651, k4_xboole_0(k2_xboole_0(k1_relat_1(C_650), B_652), B_653)))=k7_relat_1(k4_xboole_0(C_650, k7_relat_1(C_650, B_653)), A_651) | ~v1_relat_1(C_650) | ~v1_relat_1(C_650))), inference(superposition, [status(thm), theory('equality')], [c_158, c_3570])).
% 9.92/3.67  tff(c_13409, plain, (![C_654]: (k7_relat_1(k4_xboole_0(C_654, k7_relat_1(C_654, '#skF_2')), '#skF_1')=k7_relat_1(C_654, k1_xboole_0) | ~v1_relat_1(C_654) | ~v1_relat_1(C_654))), inference(superposition, [status(thm), theory('equality')], [c_925, c_13119])).
% 9.92/3.67  tff(c_32, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.92/3.67  tff(c_37, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_32])).
% 9.92/3.67  tff(c_13462, plain, (k7_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13409, c_37])).
% 9.92/3.67  tff(c_13520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_366, c_13462])).
% 9.92/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.67  
% 9.92/3.67  Inference rules
% 9.92/3.67  ----------------------
% 9.92/3.67  #Ref     : 0
% 9.92/3.67  #Sup     : 3565
% 9.92/3.67  #Fact    : 0
% 9.92/3.67  #Define  : 0
% 9.92/3.67  #Split   : 11
% 9.92/3.67  #Chain   : 0
% 9.92/3.67  #Close   : 0
% 9.92/3.67  
% 9.92/3.67  Ordering : KBO
% 9.92/3.67  
% 9.92/3.67  Simplification rules
% 9.92/3.67  ----------------------
% 9.92/3.67  #Subsume      : 755
% 9.92/3.67  #Demod        : 855
% 9.92/3.67  #Tautology    : 930
% 9.92/3.67  #SimpNegUnit  : 0
% 9.92/3.67  #BackRed      : 0
% 9.92/3.67  
% 9.92/3.67  #Partial instantiations: 0
% 9.92/3.67  #Strategies tried      : 1
% 9.92/3.67  
% 9.92/3.67  Timing (in seconds)
% 9.92/3.67  ----------------------
% 9.92/3.68  Preprocessing        : 0.30
% 9.92/3.68  Parsing              : 0.16
% 9.92/3.68  CNF conversion       : 0.02
% 9.92/3.68  Main loop            : 2.60
% 9.92/3.68  Inferencing          : 0.75
% 9.92/3.68  Reduction            : 0.97
% 9.92/3.68  Demodulation         : 0.76
% 9.92/3.68  BG Simplification    : 0.11
% 9.92/3.68  Subsumption          : 0.63
% 9.92/3.68  Abstraction          : 0.13
% 9.92/3.68  MUC search           : 0.00
% 9.92/3.68  Cooper               : 0.00
% 9.92/3.68  Total                : 2.93
% 9.92/3.68  Index Insertion      : 0.00
% 9.92/3.68  Index Deletion       : 0.00
% 9.92/3.68  Index Matching       : 0.00
% 9.92/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
