%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:41 EST 2020

% Result     : Theorem 22.68s
% Output     : CNFRefutation 22.76s
% Verified   : 
% Statistics : Number of formulae       :   64 (  76 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 106 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_243,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),k3_xboole_0(A_66,B_67))
      | r1_xboole_0(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_22,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_22])).

tff(c_169,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,k3_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [A_43,B_42,C_50] :
      ( ~ r1_xboole_0(A_43,B_42)
      | ~ r2_hidden(C_50,k3_xboole_0(B_42,A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_169])).

tff(c_258,plain,(
    ! [B_68,A_69] :
      ( ~ r1_xboole_0(B_68,A_69)
      | r1_xboole_0(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_243,c_172])).

tff(c_262,plain,(
    ! [B_70,A_71] : r1_xboole_0(B_70,k4_xboole_0(A_71,B_70)) ),
    inference(resolution,[status(thm)],[c_16,c_258])).

tff(c_14,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_xboole_0(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_269,plain,(
    ! [A_10,A_71,B_70] :
      ( r1_xboole_0(A_10,k4_xboole_0(A_71,B_70))
      | ~ r1_tarski(A_10,B_70) ) ),
    inference(resolution,[status(thm)],[c_262,c_14])).

tff(c_10,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [C_30,A_28,B_29] :
      ( k7_relat_1(C_30,k6_subset_1(A_28,B_29)) = k6_subset_1(C_30,k7_relat_1(C_30,B_29))
      | ~ r1_tarski(k1_relat_1(C_30),A_28)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_491,plain,(
    ! [C_93,A_94,B_95] :
      ( k7_relat_1(C_93,k4_xboole_0(A_94,B_95)) = k4_xboole_0(C_93,k7_relat_1(C_93,B_95))
      | ~ r1_tarski(k1_relat_1(C_93),A_94)
      | ~ v1_relat_1(C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_30])).

tff(c_497,plain,(
    ! [C_93,B_95] :
      ( k7_relat_1(C_93,k4_xboole_0(k1_relat_1(C_93),B_95)) = k4_xboole_0(C_93,k7_relat_1(C_93,B_95))
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_491])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( k1_relat_1(k7_relat_1(B_27,k6_subset_1(k1_relat_1(B_27),A_26))) = k6_subset_1(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_328,plain,(
    ! [B_83,A_84] :
      ( k1_relat_1(k7_relat_1(B_83,k4_xboole_0(k1_relat_1(B_83),A_84))) = k4_xboole_0(k1_relat_1(B_83),A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_28])).

tff(c_26,plain,(
    ! [A_23,B_25] :
      ( k7_relat_1(A_23,B_25) = k1_xboole_0
      | ~ r1_xboole_0(B_25,k1_relat_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_720,plain,(
    ! [B_123,A_124,B_125] :
      ( k7_relat_1(k7_relat_1(B_123,k4_xboole_0(k1_relat_1(B_123),A_124)),B_125) = k1_xboole_0
      | ~ r1_xboole_0(B_125,k4_xboole_0(k1_relat_1(B_123),A_124))
      | ~ v1_relat_1(k7_relat_1(B_123,k4_xboole_0(k1_relat_1(B_123),A_124)))
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_26])).

tff(c_1811,plain,(
    ! [A_173,A_174,B_175] :
      ( k7_relat_1(k7_relat_1(A_173,k4_xboole_0(k1_relat_1(A_173),A_174)),B_175) = k1_xboole_0
      | ~ r1_xboole_0(B_175,k4_xboole_0(k1_relat_1(A_173),A_174))
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_24,c_720])).

tff(c_30048,plain,(
    ! [C_550,B_551,B_552] :
      ( k7_relat_1(k4_xboole_0(C_550,k7_relat_1(C_550,B_551)),B_552) = k1_xboole_0
      | ~ r1_xboole_0(B_552,k4_xboole_0(k1_relat_1(C_550),B_551))
      | ~ v1_relat_1(C_550)
      | ~ v1_relat_1(C_550) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_1811])).

tff(c_32948,plain,(
    ! [C_565,B_566,A_567] :
      ( k7_relat_1(k4_xboole_0(C_565,k7_relat_1(C_565,B_566)),A_567) = k1_xboole_0
      | ~ v1_relat_1(C_565)
      | ~ r1_tarski(A_567,B_566) ) ),
    inference(resolution,[status(thm)],[c_269,c_30048])).

tff(c_32,plain,(
    k7_relat_1(k6_subset_1('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    k7_relat_1(k4_xboole_0('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_33540,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32948,c_38])).

tff(c_33816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_33540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.68/11.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.68/11.39  
% 22.68/11.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.68/11.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 22.68/11.40  
% 22.68/11.40  %Foreground sorts:
% 22.68/11.40  
% 22.68/11.40  
% 22.68/11.40  %Background operators:
% 22.68/11.40  
% 22.68/11.40  
% 22.68/11.40  %Foreground operators:
% 22.68/11.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.68/11.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.68/11.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.68/11.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 22.68/11.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.68/11.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.68/11.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.68/11.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.68/11.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.68/11.40  tff('#skF_2', type, '#skF_2': $i).
% 22.68/11.40  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 22.68/11.40  tff('#skF_3', type, '#skF_3': $i).
% 22.68/11.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.68/11.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.68/11.40  tff('#skF_4', type, '#skF_4': $i).
% 22.68/11.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.68/11.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.68/11.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.68/11.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.68/11.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 22.68/11.40  
% 22.76/11.41  tff(f_89, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 22.76/11.41  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 22.76/11.41  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 22.76/11.41  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 22.76/11.41  tff(f_61, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 22.76/11.41  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 22.76/11.41  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.76/11.41  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 22.76/11.41  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 22.76/11.41  tff(f_65, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 22.76/11.41  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 22.76/11.41  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 22.76/11.41  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.76/11.41  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.76/11.41  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.76/11.41  tff(c_243, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), k3_xboole_0(A_66, B_67)) | r1_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.76/11.41  tff(c_18, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.76/11.41  tff(c_86, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.76/11.41  tff(c_101, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_18, c_86])).
% 22.76/11.41  tff(c_22, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.76/11.41  tff(c_107, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_101, c_22])).
% 22.76/11.41  tff(c_169, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.76/11.41  tff(c_172, plain, (![A_43, B_42, C_50]: (~r1_xboole_0(A_43, B_42) | ~r2_hidden(C_50, k3_xboole_0(B_42, A_43)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_169])).
% 22.76/11.41  tff(c_258, plain, (![B_68, A_69]: (~r1_xboole_0(B_68, A_69) | r1_xboole_0(A_69, B_68))), inference(resolution, [status(thm)], [c_243, c_172])).
% 22.76/11.41  tff(c_262, plain, (![B_70, A_71]: (r1_xboole_0(B_70, k4_xboole_0(A_71, B_70)))), inference(resolution, [status(thm)], [c_16, c_258])).
% 22.76/11.41  tff(c_14, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_xboole_0(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.76/11.41  tff(c_269, plain, (![A_10, A_71, B_70]: (r1_xboole_0(A_10, k4_xboole_0(A_71, B_70)) | ~r1_tarski(A_10, B_70))), inference(resolution, [status(thm)], [c_262, c_14])).
% 22.76/11.41  tff(c_10, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.76/11.41  tff(c_20, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.76/11.41  tff(c_30, plain, (![C_30, A_28, B_29]: (k7_relat_1(C_30, k6_subset_1(A_28, B_29))=k6_subset_1(C_30, k7_relat_1(C_30, B_29)) | ~r1_tarski(k1_relat_1(C_30), A_28) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 22.76/11.41  tff(c_491, plain, (![C_93, A_94, B_95]: (k7_relat_1(C_93, k4_xboole_0(A_94, B_95))=k4_xboole_0(C_93, k7_relat_1(C_93, B_95)) | ~r1_tarski(k1_relat_1(C_93), A_94) | ~v1_relat_1(C_93))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_30])).
% 22.76/11.41  tff(c_497, plain, (![C_93, B_95]: (k7_relat_1(C_93, k4_xboole_0(k1_relat_1(C_93), B_95))=k4_xboole_0(C_93, k7_relat_1(C_93, B_95)) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_10, c_491])).
% 22.76/11.41  tff(c_24, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.76/11.41  tff(c_28, plain, (![B_27, A_26]: (k1_relat_1(k7_relat_1(B_27, k6_subset_1(k1_relat_1(B_27), A_26)))=k6_subset_1(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 22.76/11.41  tff(c_328, plain, (![B_83, A_84]: (k1_relat_1(k7_relat_1(B_83, k4_xboole_0(k1_relat_1(B_83), A_84)))=k4_xboole_0(k1_relat_1(B_83), A_84) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_28])).
% 22.76/11.41  tff(c_26, plain, (![A_23, B_25]: (k7_relat_1(A_23, B_25)=k1_xboole_0 | ~r1_xboole_0(B_25, k1_relat_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.76/11.41  tff(c_720, plain, (![B_123, A_124, B_125]: (k7_relat_1(k7_relat_1(B_123, k4_xboole_0(k1_relat_1(B_123), A_124)), B_125)=k1_xboole_0 | ~r1_xboole_0(B_125, k4_xboole_0(k1_relat_1(B_123), A_124)) | ~v1_relat_1(k7_relat_1(B_123, k4_xboole_0(k1_relat_1(B_123), A_124))) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_328, c_26])).
% 22.76/11.41  tff(c_1811, plain, (![A_173, A_174, B_175]: (k7_relat_1(k7_relat_1(A_173, k4_xboole_0(k1_relat_1(A_173), A_174)), B_175)=k1_xboole_0 | ~r1_xboole_0(B_175, k4_xboole_0(k1_relat_1(A_173), A_174)) | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_24, c_720])).
% 22.76/11.41  tff(c_30048, plain, (![C_550, B_551, B_552]: (k7_relat_1(k4_xboole_0(C_550, k7_relat_1(C_550, B_551)), B_552)=k1_xboole_0 | ~r1_xboole_0(B_552, k4_xboole_0(k1_relat_1(C_550), B_551)) | ~v1_relat_1(C_550) | ~v1_relat_1(C_550))), inference(superposition, [status(thm), theory('equality')], [c_497, c_1811])).
% 22.76/11.41  tff(c_32948, plain, (![C_565, B_566, A_567]: (k7_relat_1(k4_xboole_0(C_565, k7_relat_1(C_565, B_566)), A_567)=k1_xboole_0 | ~v1_relat_1(C_565) | ~r1_tarski(A_567, B_566))), inference(resolution, [status(thm)], [c_269, c_30048])).
% 22.76/11.41  tff(c_32, plain, (k7_relat_1(k6_subset_1('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.76/11.41  tff(c_38, plain, (k7_relat_1(k4_xboole_0('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_32])).
% 22.76/11.41  tff(c_33540, plain, (~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32948, c_38])).
% 22.76/11.41  tff(c_33816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_33540])).
% 22.76/11.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.76/11.41  
% 22.76/11.41  Inference rules
% 22.76/11.41  ----------------------
% 22.76/11.41  #Ref     : 0
% 22.76/11.41  #Sup     : 9029
% 22.76/11.41  #Fact    : 0
% 22.76/11.41  #Define  : 0
% 22.76/11.41  #Split   : 16
% 22.76/11.41  #Chain   : 0
% 22.76/11.41  #Close   : 0
% 22.76/11.41  
% 22.76/11.41  Ordering : KBO
% 22.76/11.41  
% 22.76/11.41  Simplification rules
% 22.76/11.41  ----------------------
% 22.76/11.41  #Subsume      : 909
% 22.76/11.41  #Demod        : 8398
% 22.76/11.41  #Tautology    : 1007
% 22.76/11.41  #SimpNegUnit  : 12
% 22.76/11.41  #BackRed      : 28
% 22.76/11.41  
% 22.76/11.41  #Partial instantiations: 0
% 22.76/11.41  #Strategies tried      : 1
% 22.76/11.41  
% 22.76/11.41  Timing (in seconds)
% 22.76/11.41  ----------------------
% 22.76/11.41  Preprocessing        : 0.32
% 22.76/11.41  Parsing              : 0.17
% 22.76/11.41  CNF conversion       : 0.02
% 22.76/11.41  Main loop            : 10.32
% 22.76/11.41  Inferencing          : 3.56
% 22.76/11.41  Reduction            : 2.95
% 22.76/11.41  Demodulation         : 2.34
% 22.76/11.41  BG Simplification    : 0.66
% 22.76/11.41  Subsumption          : 2.78
% 22.76/11.41  Abstraction          : 1.05
% 22.76/11.41  MUC search           : 0.00
% 22.76/11.41  Cooper               : 0.00
% 22.76/11.41  Total                : 10.67
% 22.76/11.41  Index Insertion      : 0.00
% 22.76/11.41  Index Deletion       : 0.00
% 22.76/11.41  Index Matching       : 0.00
% 22.76/11.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
