%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:42 EST 2020

% Result     : Theorem 21.09s
% Output     : CNFRefutation 21.14s
% Verified   : 
% Statistics : Number of formulae       :   62 (  73 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 (  97 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_62,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_39,plain,(
    ! [A_33] :
      ( k7_relat_1(A_33,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_43,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_39])).

tff(c_16,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,k4_xboole_0(C_16,B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_171,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_193,plain,(
    ! [A_58,B_59,B_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | r1_tarski(k3_xboole_0(A_58,B_59),B_60) ) ),
    inference(resolution,[status(thm)],[c_171,c_10])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_205,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_193,c_12])).

tff(c_209,plain,(
    ! [A_14,C_16,B_15] :
      ( k3_xboole_0(A_14,k4_xboole_0(C_16,B_15)) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_205])).

tff(c_18,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_90])).

tff(c_22,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_111,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_22])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [C_29,A_27,B_28] :
      ( k7_relat_1(C_29,k6_subset_1(A_27,B_28)) = k6_subset_1(C_29,k7_relat_1(C_29,B_28))
      | ~ r1_tarski(k1_relat_1(C_29),A_27)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_393,plain,(
    ! [C_86,A_87,B_88] :
      ( k7_relat_1(C_86,k4_xboole_0(A_87,B_88)) = k4_xboole_0(C_86,k7_relat_1(C_86,B_88))
      | ~ r1_tarski(k1_relat_1(C_86),A_87)
      | ~ v1_relat_1(C_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_28])).

tff(c_1001,plain,(
    ! [C_138,B_139,B_140] :
      ( k7_relat_1(C_138,k4_xboole_0(k2_xboole_0(k1_relat_1(C_138),B_139),B_140)) = k4_xboole_0(C_138,k7_relat_1(C_138,B_140))
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_14,c_393])).

tff(c_24,plain,(
    ! [C_25,A_23,B_24] :
      ( k7_relat_1(k7_relat_1(C_25,A_23),B_24) = k7_relat_1(C_25,k3_xboole_0(A_23,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1759,plain,(
    ! [C_200,B_201,B_202,B_203] :
      ( k7_relat_1(C_200,k3_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_200),B_201),B_202),B_203)) = k7_relat_1(k4_xboole_0(C_200,k7_relat_1(C_200,B_202)),B_203)
      | ~ v1_relat_1(C_200)
      | ~ v1_relat_1(C_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_24])).

tff(c_10387,plain,(
    ! [C_366,A_367,B_368,B_369] :
      ( k7_relat_1(C_366,k3_xboole_0(A_367,k4_xboole_0(k2_xboole_0(k1_relat_1(C_366),B_368),B_369))) = k7_relat_1(k4_xboole_0(C_366,k7_relat_1(C_366,B_369)),A_367)
      | ~ v1_relat_1(C_366)
      | ~ v1_relat_1(C_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_1759])).

tff(c_37076,plain,(
    ! [C_714,B_715,A_716] :
      ( k7_relat_1(k4_xboole_0(C_714,k7_relat_1(C_714,B_715)),A_716) = k7_relat_1(C_714,k1_xboole_0)
      | ~ v1_relat_1(C_714)
      | ~ v1_relat_1(C_714)
      | ~ r1_tarski(A_716,B_715) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_10387])).

tff(c_30,plain,(
    k7_relat_1(k6_subset_1('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_37226,plain,
    ( k7_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37076,c_36])).

tff(c_37744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_34,c_43,c_37226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.09/12.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.14/12.86  
% 21.14/12.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.14/12.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 21.14/12.87  
% 21.14/12.87  %Foreground sorts:
% 21.14/12.87  
% 21.14/12.87  
% 21.14/12.87  %Background operators:
% 21.14/12.87  
% 21.14/12.87  
% 21.14/12.87  %Foreground operators:
% 21.14/12.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.14/12.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.14/12.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.14/12.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 21.14/12.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.14/12.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.14/12.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.14/12.87  tff('#skF_5', type, '#skF_5': $i).
% 21.14/12.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.14/12.87  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 21.14/12.87  tff('#skF_3', type, '#skF_3': $i).
% 21.14/12.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.14/12.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.14/12.87  tff('#skF_4', type, '#skF_4': $i).
% 21.14/12.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.14/12.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 21.14/12.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.14/12.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.14/12.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 21.14/12.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.14/12.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.14/12.87  
% 21.14/12.88  tff(f_83, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 21.14/12.88  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 21.14/12.88  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 21.14/12.88  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 21.14/12.88  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 21.14/12.88  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 21.14/12.88  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 21.14/12.88  tff(f_62, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 21.14/12.88  tff(f_52, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 21.14/12.88  tff(f_60, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 21.14/12.88  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 21.14/12.88  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 21.14/12.88  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.14/12.88  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.14/12.88  tff(c_39, plain, (![A_33]: (k7_relat_1(A_33, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 21.14/12.88  tff(c_43, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_39])).
% 21.14/12.88  tff(c_16, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, k4_xboole_0(C_16, B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.14/12.88  tff(c_171, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.14/12.88  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.14/12.88  tff(c_193, plain, (![A_58, B_59, B_60]: (~r1_xboole_0(A_58, B_59) | r1_tarski(k3_xboole_0(A_58, B_59), B_60))), inference(resolution, [status(thm)], [c_171, c_10])).
% 21.14/12.88  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 21.14/12.88  tff(c_205, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(A_61, B_62))), inference(resolution, [status(thm)], [c_193, c_12])).
% 21.14/12.88  tff(c_209, plain, (![A_14, C_16, B_15]: (k3_xboole_0(A_14, k4_xboole_0(C_16, B_15))=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_16, c_205])).
% 21.14/12.88  tff(c_18, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.14/12.88  tff(c_90, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 21.14/12.88  tff(c_105, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_18, c_90])).
% 21.14/12.88  tff(c_22, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 21.14/12.88  tff(c_111, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_105, c_22])).
% 21.14/12.88  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.14/12.88  tff(c_20, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 21.14/12.88  tff(c_28, plain, (![C_29, A_27, B_28]: (k7_relat_1(C_29, k6_subset_1(A_27, B_28))=k6_subset_1(C_29, k7_relat_1(C_29, B_28)) | ~r1_tarski(k1_relat_1(C_29), A_27) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 21.14/12.88  tff(c_393, plain, (![C_86, A_87, B_88]: (k7_relat_1(C_86, k4_xboole_0(A_87, B_88))=k4_xboole_0(C_86, k7_relat_1(C_86, B_88)) | ~r1_tarski(k1_relat_1(C_86), A_87) | ~v1_relat_1(C_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_28])).
% 21.14/12.88  tff(c_1001, plain, (![C_138, B_139, B_140]: (k7_relat_1(C_138, k4_xboole_0(k2_xboole_0(k1_relat_1(C_138), B_139), B_140))=k4_xboole_0(C_138, k7_relat_1(C_138, B_140)) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_14, c_393])).
% 21.14/12.88  tff(c_24, plain, (![C_25, A_23, B_24]: (k7_relat_1(k7_relat_1(C_25, A_23), B_24)=k7_relat_1(C_25, k3_xboole_0(A_23, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 21.14/12.88  tff(c_1759, plain, (![C_200, B_201, B_202, B_203]: (k7_relat_1(C_200, k3_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_200), B_201), B_202), B_203))=k7_relat_1(k4_xboole_0(C_200, k7_relat_1(C_200, B_202)), B_203) | ~v1_relat_1(C_200) | ~v1_relat_1(C_200))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_24])).
% 21.14/12.88  tff(c_10387, plain, (![C_366, A_367, B_368, B_369]: (k7_relat_1(C_366, k3_xboole_0(A_367, k4_xboole_0(k2_xboole_0(k1_relat_1(C_366), B_368), B_369)))=k7_relat_1(k4_xboole_0(C_366, k7_relat_1(C_366, B_369)), A_367) | ~v1_relat_1(C_366) | ~v1_relat_1(C_366))), inference(superposition, [status(thm), theory('equality')], [c_111, c_1759])).
% 21.14/12.88  tff(c_37076, plain, (![C_714, B_715, A_716]: (k7_relat_1(k4_xboole_0(C_714, k7_relat_1(C_714, B_715)), A_716)=k7_relat_1(C_714, k1_xboole_0) | ~v1_relat_1(C_714) | ~v1_relat_1(C_714) | ~r1_tarski(A_716, B_715))), inference(superposition, [status(thm), theory('equality')], [c_209, c_10387])).
% 21.14/12.88  tff(c_30, plain, (k7_relat_1(k6_subset_1('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.14/12.88  tff(c_36, plain, (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 21.14/12.88  tff(c_37226, plain, (k7_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37076, c_36])).
% 21.14/12.88  tff(c_37744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_34, c_43, c_37226])).
% 21.14/12.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.14/12.88  
% 21.14/12.88  Inference rules
% 21.14/12.88  ----------------------
% 21.14/12.88  #Ref     : 0
% 21.14/12.88  #Sup     : 9579
% 21.14/12.88  #Fact    : 0
% 21.14/12.88  #Define  : 0
% 21.14/12.88  #Split   : 10
% 21.14/12.88  #Chain   : 0
% 21.14/12.88  #Close   : 0
% 21.14/12.88  
% 21.14/12.88  Ordering : KBO
% 21.14/12.88  
% 21.14/12.88  Simplification rules
% 21.14/12.88  ----------------------
% 21.14/12.88  #Subsume      : 3162
% 21.14/12.88  #Demod        : 6249
% 21.14/12.88  #Tautology    : 1765
% 21.14/12.88  #SimpNegUnit  : 21
% 21.14/12.88  #BackRed      : 16
% 21.14/12.88  
% 21.14/12.88  #Partial instantiations: 0
% 21.14/12.88  #Strategies tried      : 1
% 21.14/12.88  
% 21.14/12.88  Timing (in seconds)
% 21.14/12.88  ----------------------
% 21.14/12.88  Preprocessing        : 0.32
% 21.14/12.88  Parsing              : 0.18
% 21.14/12.88  CNF conversion       : 0.02
% 21.14/12.88  Main loop            : 11.72
% 21.14/12.88  Inferencing          : 1.80
% 21.14/12.88  Reduction            : 7.80
% 21.14/12.88  Demodulation         : 7.27
% 21.14/12.88  BG Simplification    : 0.25
% 21.14/12.88  Subsumption          : 1.62
% 21.14/12.88  Abstraction          : 0.46
% 21.14/12.88  MUC search           : 0.00
% 21.14/12.88  Cooper               : 0.00
% 21.14/12.88  Total                : 12.07
% 21.14/12.88  Index Insertion      : 0.00
% 21.14/12.88  Index Deletion       : 0.00
% 21.14/12.88  Index Matching       : 0.00
% 21.14/12.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
