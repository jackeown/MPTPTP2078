%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:42 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :   71 (  79 expanded)
%              Number of leaves         :   36 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 (  98 expanded)
%              Number of equality atoms :   28 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_309,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_327,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = k4_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_309])).

tff(c_330,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_327])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | ~ r1_xboole_0(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [B_21,A_20] : r1_xboole_0(B_21,k4_xboole_0(A_20,B_21)) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_261,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_290,plain,(
    ! [A_70,B_71] :
      ( ~ r1_xboole_0(A_70,B_71)
      | k3_xboole_0(A_70,B_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_261])).

tff(c_340,plain,(
    ! [B_75,A_76] : k3_xboole_0(B_75,k4_xboole_0(A_76,B_75)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_290])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_345,plain,(
    ! [B_75,A_76] : k4_xboole_0(B_75,k4_xboole_0(A_76,B_75)) = k5_xboole_0(B_75,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_10])).

tff(c_361,plain,(
    ! [B_75,A_76] : k4_xboole_0(B_75,k4_xboole_0(A_76,B_75)) = B_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_345])).

tff(c_501,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_xboole_0(A_82,C_83)
      | ~ r1_tarski(A_82,k4_xboole_0(B_84,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_759,plain,(
    ! [A_110,A_111,B_112] :
      ( r1_xboole_0(A_110,k4_xboole_0(A_111,B_112))
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_501])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_782,plain,(
    ! [A_111,B_112,A_110] :
      ( r1_xboole_0(k4_xboole_0(A_111,B_112),A_110)
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(resolution,[status(thm)],[c_759,c_2])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_251,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(A_63,C_64)
      | ~ r1_tarski(k2_xboole_0(A_63,B_65),C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_256,plain,(
    ! [A_63,B_65,B_23] : r1_tarski(A_63,k2_xboole_0(k2_xboole_0(A_63,B_65),B_23)) ),
    inference(resolution,[status(thm)],[c_24,c_251])).

tff(c_28,plain,(
    ! [A_26,B_27] : k6_subset_1(A_26,B_27) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [C_35,A_33,B_34] :
      ( k7_relat_1(C_35,k6_subset_1(A_33,B_34)) = k6_subset_1(C_35,k7_relat_1(C_35,B_34))
      | ~ r1_tarski(k1_relat_1(C_35),A_33)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_810,plain,(
    ! [C_116,A_117,B_118] :
      ( k7_relat_1(C_116,k4_xboole_0(A_117,B_118)) = k4_xboole_0(C_116,k7_relat_1(C_116,B_118))
      | ~ r1_tarski(k1_relat_1(C_116),A_117)
      | ~ v1_relat_1(C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_34])).

tff(c_2731,plain,(
    ! [C_260,B_261,B_262,B_263] :
      ( k7_relat_1(C_260,k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_relat_1(C_260),B_261),B_262),B_263)) = k4_xboole_0(C_260,k7_relat_1(C_260,B_263))
      | ~ v1_relat_1(C_260) ) ),
    inference(resolution,[status(thm)],[c_256,c_810])).

tff(c_32,plain,(
    ! [C_32,A_30,B_31] :
      ( k7_relat_1(k7_relat_1(C_32,A_30),B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4343,plain,(
    ! [B_425,B_424,C_422,B_423,B_426] :
      ( k7_relat_1(k4_xboole_0(C_422,k7_relat_1(C_422,B_425)),B_424) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_relat_1(C_422),B_426),B_423),B_425),B_424)
      | ~ v1_relat_1(C_422)
      | ~ v1_relat_1(C_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2731,c_32])).

tff(c_8091,plain,(
    ! [C_683,B_684,A_685] :
      ( k7_relat_1(k4_xboole_0(C_683,k7_relat_1(C_683,B_684)),A_685) = k1_xboole_0
      | ~ v1_relat_1(C_683)
      | ~ r1_tarski(A_685,B_684) ) ),
    inference(resolution,[status(thm)],[c_782,c_4343])).

tff(c_36,plain,(
    k7_relat_1(k6_subset_1('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_8209,plain,
    ( ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8091,c_42])).

tff(c_8343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_8209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:27:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.29/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.66  
% 7.29/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 7.29/2.66  
% 7.29/2.66  %Foreground sorts:
% 7.29/2.66  
% 7.29/2.66  
% 7.29/2.66  %Background operators:
% 7.29/2.66  
% 7.29/2.66  
% 7.29/2.66  %Foreground operators:
% 7.29/2.66  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.29/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.29/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.29/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.29/2.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.29/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.29/2.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.29/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.29/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.29/2.66  tff('#skF_5', type, '#skF_5': $i).
% 7.29/2.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.29/2.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.29/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.29/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.29/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.29/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.29/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.29/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.29/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.29/2.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.29/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.29/2.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.29/2.66  
% 7.43/2.68  tff(f_96, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 7.43/2.68  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.43/2.68  tff(f_65, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.43/2.68  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.43/2.68  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.43/2.68  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.43/2.68  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.43/2.68  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.43/2.68  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.43/2.68  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.43/2.68  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.43/2.68  tff(f_75, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.43/2.68  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 7.43/2.68  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 7.43/2.68  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.43/2.68  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.43/2.68  tff(c_20, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.43/2.68  tff(c_18, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.43/2.68  tff(c_309, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.43/2.68  tff(c_327, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=k4_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_309])).
% 7.43/2.68  tff(c_330, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_327])).
% 7.43/2.68  tff(c_22, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.43/2.68  tff(c_66, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | ~r1_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.43/2.68  tff(c_72, plain, (![B_21, A_20]: (r1_xboole_0(B_21, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_22, c_66])).
% 7.43/2.68  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.43/2.68  tff(c_261, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.43/2.68  tff(c_290, plain, (![A_70, B_71]: (~r1_xboole_0(A_70, B_71) | k3_xboole_0(A_70, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_261])).
% 7.43/2.68  tff(c_340, plain, (![B_75, A_76]: (k3_xboole_0(B_75, k4_xboole_0(A_76, B_75))=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_290])).
% 7.43/2.68  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.43/2.68  tff(c_345, plain, (![B_75, A_76]: (k4_xboole_0(B_75, k4_xboole_0(A_76, B_75))=k5_xboole_0(B_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_340, c_10])).
% 7.43/2.68  tff(c_361, plain, (![B_75, A_76]: (k4_xboole_0(B_75, k4_xboole_0(A_76, B_75))=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_330, c_345])).
% 7.43/2.68  tff(c_501, plain, (![A_82, C_83, B_84]: (r1_xboole_0(A_82, C_83) | ~r1_tarski(A_82, k4_xboole_0(B_84, C_83)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.43/2.68  tff(c_759, plain, (![A_110, A_111, B_112]: (r1_xboole_0(A_110, k4_xboole_0(A_111, B_112)) | ~r1_tarski(A_110, B_112))), inference(superposition, [status(thm), theory('equality')], [c_361, c_501])).
% 7.43/2.68  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.43/2.68  tff(c_782, plain, (![A_111, B_112, A_110]: (r1_xboole_0(k4_xboole_0(A_111, B_112), A_110) | ~r1_tarski(A_110, B_112))), inference(resolution, [status(thm)], [c_759, c_2])).
% 7.43/2.68  tff(c_24, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.43/2.68  tff(c_251, plain, (![A_63, C_64, B_65]: (r1_tarski(A_63, C_64) | ~r1_tarski(k2_xboole_0(A_63, B_65), C_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.43/2.68  tff(c_256, plain, (![A_63, B_65, B_23]: (r1_tarski(A_63, k2_xboole_0(k2_xboole_0(A_63, B_65), B_23)))), inference(resolution, [status(thm)], [c_24, c_251])).
% 7.43/2.68  tff(c_28, plain, (![A_26, B_27]: (k6_subset_1(A_26, B_27)=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.43/2.68  tff(c_34, plain, (![C_35, A_33, B_34]: (k7_relat_1(C_35, k6_subset_1(A_33, B_34))=k6_subset_1(C_35, k7_relat_1(C_35, B_34)) | ~r1_tarski(k1_relat_1(C_35), A_33) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.43/2.68  tff(c_810, plain, (![C_116, A_117, B_118]: (k7_relat_1(C_116, k4_xboole_0(A_117, B_118))=k4_xboole_0(C_116, k7_relat_1(C_116, B_118)) | ~r1_tarski(k1_relat_1(C_116), A_117) | ~v1_relat_1(C_116))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_34])).
% 7.43/2.68  tff(c_2731, plain, (![C_260, B_261, B_262, B_263]: (k7_relat_1(C_260, k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_relat_1(C_260), B_261), B_262), B_263))=k4_xboole_0(C_260, k7_relat_1(C_260, B_263)) | ~v1_relat_1(C_260))), inference(resolution, [status(thm)], [c_256, c_810])).
% 7.43/2.68  tff(c_32, plain, (![C_32, A_30, B_31]: (k7_relat_1(k7_relat_1(C_32, A_30), B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.43/2.68  tff(c_4343, plain, (![B_425, B_424, C_422, B_423, B_426]: (k7_relat_1(k4_xboole_0(C_422, k7_relat_1(C_422, B_425)), B_424)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_relat_1(C_422), B_426), B_423), B_425), B_424) | ~v1_relat_1(C_422) | ~v1_relat_1(C_422))), inference(superposition, [status(thm), theory('equality')], [c_2731, c_32])).
% 7.43/2.68  tff(c_8091, plain, (![C_683, B_684, A_685]: (k7_relat_1(k4_xboole_0(C_683, k7_relat_1(C_683, B_684)), A_685)=k1_xboole_0 | ~v1_relat_1(C_683) | ~r1_tarski(A_685, B_684))), inference(resolution, [status(thm)], [c_782, c_4343])).
% 7.43/2.68  tff(c_36, plain, (k7_relat_1(k6_subset_1('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.43/2.68  tff(c_42, plain, (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 7.43/2.68  tff(c_8209, plain, (~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8091, c_42])).
% 7.43/2.68  tff(c_8343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_8209])).
% 7.43/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.43/2.68  
% 7.43/2.68  Inference rules
% 7.43/2.68  ----------------------
% 7.43/2.68  #Ref     : 0
% 7.43/2.68  #Sup     : 2236
% 7.43/2.68  #Fact    : 0
% 7.43/2.68  #Define  : 0
% 7.43/2.68  #Split   : 13
% 7.43/2.68  #Chain   : 0
% 7.43/2.68  #Close   : 0
% 7.43/2.68  
% 7.43/2.68  Ordering : KBO
% 7.43/2.68  
% 7.43/2.68  Simplification rules
% 7.43/2.68  ----------------------
% 7.43/2.68  #Subsume      : 786
% 7.43/2.68  #Demod        : 520
% 7.43/2.68  #Tautology    : 578
% 7.43/2.68  #SimpNegUnit  : 34
% 7.43/2.68  #BackRed      : 0
% 7.43/2.68  
% 7.43/2.68  #Partial instantiations: 0
% 7.43/2.68  #Strategies tried      : 1
% 7.43/2.68  
% 7.43/2.68  Timing (in seconds)
% 7.43/2.68  ----------------------
% 7.43/2.68  Preprocessing        : 0.30
% 7.43/2.68  Parsing              : 0.16
% 7.43/2.68  CNF conversion       : 0.02
% 7.43/2.68  Main loop            : 1.61
% 7.43/2.68  Inferencing          : 0.47
% 7.43/2.68  Reduction            : 0.57
% 7.43/2.68  Demodulation         : 0.42
% 7.43/2.68  BG Simplification    : 0.05
% 7.43/2.68  Subsumption          : 0.41
% 7.43/2.68  Abstraction          : 0.06
% 7.43/2.68  MUC search           : 0.00
% 7.43/2.68  Cooper               : 0.00
% 7.43/2.68  Total                : 1.95
% 7.43/2.68  Index Insertion      : 0.00
% 7.43/2.68  Index Deletion       : 0.00
% 7.43/2.68  Index Matching       : 0.00
% 7.43/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
