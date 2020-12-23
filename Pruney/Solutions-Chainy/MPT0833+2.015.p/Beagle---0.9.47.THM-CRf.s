%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:47 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 108 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 186 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_52,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_88,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_94,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_98,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_94])).

tff(c_20,plain,(
    ! [C_13,A_11,B_12] :
      ( r1_tarski(k2_zfmisc_1(C_13,A_11),k2_zfmisc_1(C_13,B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_67])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_342,plain,(
    ! [C_116,B_117,A_118] :
      ( r2_hidden(C_116,B_117)
      | ~ r1_tarski(k1_zfmisc_1(A_118),B_117)
      | ~ r1_tarski(C_116,A_118) ) ),
    inference(resolution,[status(thm)],[c_10,c_142])).

tff(c_371,plain,(
    ! [C_123,B_124,A_125] :
      ( r2_hidden(C_123,k1_zfmisc_1(B_124))
      | ~ r1_tarski(C_123,A_125)
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(resolution,[status(thm)],[c_24,c_342])).

tff(c_468,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_7',k1_zfmisc_1(B_134))
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),B_134) ) ),
    inference(resolution,[status(thm)],[c_71,c_371])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_480,plain,(
    ! [B_135] :
      ( r1_tarski('#skF_7',B_135)
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),B_135) ) ),
    inference(resolution,[status(thm)],[c_468,c_8])).

tff(c_498,plain,(
    ! [B_138] :
      ( r1_tarski('#skF_7',k2_zfmisc_1('#skF_4',B_138))
      | ~ r1_tarski('#skF_5',B_138) ) ),
    inference(resolution,[status(thm)],[c_20,c_480])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_149,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_162,plain,(
    ! [A_18,B_69,A_70] :
      ( v5_relat_1(A_18,B_69)
      | ~ r1_tarski(A_18,k2_zfmisc_1(A_70,B_69)) ) ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_517,plain,(
    ! [B_139] :
      ( v5_relat_1('#skF_7',B_139)
      | ~ r1_tarski('#skF_5',B_139) ) ),
    inference(resolution,[status(thm)],[c_498,c_162])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_246,plain,(
    ! [A_94,B_95] :
      ( k8_relat_1(A_94,B_95) = B_95
      | ~ r1_tarski(k2_relat_1(B_95),A_94)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_254,plain,(
    ! [A_23,B_24] :
      ( k8_relat_1(A_23,B_24) = B_24
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_36,c_246])).

tff(c_522,plain,(
    ! [B_139] :
      ( k8_relat_1(B_139,'#skF_7') = '#skF_7'
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski('#skF_5',B_139) ) ),
    inference(resolution,[status(thm)],[c_517,c_254])).

tff(c_529,plain,(
    ! [B_140] :
      ( k8_relat_1(B_140,'#skF_7') = '#skF_7'
      | ~ r1_tarski('#skF_5',B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_522])).

tff(c_543,plain,(
    k8_relat_1('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_52,c_529])).

tff(c_778,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k6_relset_1(A_159,B_160,C_161,D_162) = k8_relat_1(C_161,D_162)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_799,plain,(
    ! [C_161] : k6_relset_1('#skF_4','#skF_5',C_161,'#skF_7') = k8_relat_1(C_161,'#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_778])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_4','#skF_5',k6_relset_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_801,plain,(
    ~ r2_relset_1('#skF_4','#skF_5',k8_relat_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_50])).

tff(c_802,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_801])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden('#skF_1'(A_58,B_59),B_59)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_635,plain,(
    ! [B_151] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(B_151))
      | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),B_151) ) ),
    inference(resolution,[status(thm)],[c_468,c_26])).

tff(c_649,plain,(
    ! [B_12] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_12)))
      | ~ r1_tarski('#skF_5',B_12) ) ),
    inference(resolution,[status(thm)],[c_20,c_635])).

tff(c_854,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( r2_relset_1(A_172,B_173,C_174,C_174)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_879,plain,(
    ! [C_176] :
      ( r2_relset_1('#skF_4','#skF_5',C_176,C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_54,c_854])).

tff(c_882,plain,
    ( r2_relset_1('#skF_4','#skF_5','#skF_7','#skF_7')
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_649,c_879])).

tff(c_899,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_882])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_802,c_899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.50  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.21/1.50  
% 3.21/1.50  %Foreground sorts:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Background operators:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Foreground operators:
% 3.21/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.21/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.21/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.21/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.50  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 3.21/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.21/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.21/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.21/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.21/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.21/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.50  
% 3.42/1.51  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 3.42/1.51  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.42/1.51  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.42/1.51  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.42/1.51  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.42/1.51  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.42/1.51  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.42/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.42/1.51  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.51  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.42/1.51  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 3.42/1.51  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 3.42/1.51  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.42/1.51  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.42/1.51  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.42/1.51  tff(c_38, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.42/1.51  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.42/1.51  tff(c_88, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.51  tff(c_94, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_88])).
% 3.42/1.51  tff(c_98, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_94])).
% 3.42/1.51  tff(c_20, plain, (![C_13, A_11, B_12]: (r1_tarski(k2_zfmisc_1(C_13, A_11), k2_zfmisc_1(C_13, B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.51  tff(c_67, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.51  tff(c_71, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_67])).
% 3.42/1.51  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.42/1.51  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.51  tff(c_142, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.42/1.51  tff(c_342, plain, (![C_116, B_117, A_118]: (r2_hidden(C_116, B_117) | ~r1_tarski(k1_zfmisc_1(A_118), B_117) | ~r1_tarski(C_116, A_118))), inference(resolution, [status(thm)], [c_10, c_142])).
% 3.42/1.51  tff(c_371, plain, (![C_123, B_124, A_125]: (r2_hidden(C_123, k1_zfmisc_1(B_124)) | ~r1_tarski(C_123, A_125) | ~r1_tarski(A_125, B_124))), inference(resolution, [status(thm)], [c_24, c_342])).
% 3.42/1.51  tff(c_468, plain, (![B_134]: (r2_hidden('#skF_7', k1_zfmisc_1(B_134)) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), B_134))), inference(resolution, [status(thm)], [c_71, c_371])).
% 3.42/1.51  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.51  tff(c_480, plain, (![B_135]: (r1_tarski('#skF_7', B_135) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), B_135))), inference(resolution, [status(thm)], [c_468, c_8])).
% 3.42/1.51  tff(c_498, plain, (![B_138]: (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', B_138)) | ~r1_tarski('#skF_5', B_138))), inference(resolution, [status(thm)], [c_20, c_480])).
% 3.42/1.51  tff(c_30, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.51  tff(c_149, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.42/1.51  tff(c_162, plain, (![A_18, B_69, A_70]: (v5_relat_1(A_18, B_69) | ~r1_tarski(A_18, k2_zfmisc_1(A_70, B_69)))), inference(resolution, [status(thm)], [c_30, c_149])).
% 3.42/1.51  tff(c_517, plain, (![B_139]: (v5_relat_1('#skF_7', B_139) | ~r1_tarski('#skF_5', B_139))), inference(resolution, [status(thm)], [c_498, c_162])).
% 3.42/1.51  tff(c_36, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(B_24), A_23) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.42/1.51  tff(c_246, plain, (![A_94, B_95]: (k8_relat_1(A_94, B_95)=B_95 | ~r1_tarski(k2_relat_1(B_95), A_94) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.42/1.51  tff(c_254, plain, (![A_23, B_24]: (k8_relat_1(A_23, B_24)=B_24 | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_36, c_246])).
% 3.42/1.51  tff(c_522, plain, (![B_139]: (k8_relat_1(B_139, '#skF_7')='#skF_7' | ~v1_relat_1('#skF_7') | ~r1_tarski('#skF_5', B_139))), inference(resolution, [status(thm)], [c_517, c_254])).
% 3.42/1.51  tff(c_529, plain, (![B_140]: (k8_relat_1(B_140, '#skF_7')='#skF_7' | ~r1_tarski('#skF_5', B_140))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_522])).
% 3.42/1.51  tff(c_543, plain, (k8_relat_1('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_52, c_529])).
% 3.42/1.51  tff(c_778, plain, (![A_159, B_160, C_161, D_162]: (k6_relset_1(A_159, B_160, C_161, D_162)=k8_relat_1(C_161, D_162) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.42/1.51  tff(c_799, plain, (![C_161]: (k6_relset_1('#skF_4', '#skF_5', C_161, '#skF_7')=k8_relat_1(C_161, '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_778])).
% 3.42/1.51  tff(c_50, plain, (~r2_relset_1('#skF_4', '#skF_5', k6_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.42/1.51  tff(c_801, plain, (~r2_relset_1('#skF_4', '#skF_5', k8_relat_1('#skF_6', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_50])).
% 3.42/1.51  tff(c_802, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_543, c_801])).
% 3.42/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.42/1.51  tff(c_99, plain, (![A_58, B_59]: (~r2_hidden('#skF_1'(A_58, B_59), B_59) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.42/1.51  tff(c_108, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_99])).
% 3.42/1.51  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.42/1.51  tff(c_635, plain, (![B_151]: (m1_subset_1('#skF_7', k1_zfmisc_1(B_151)) | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), B_151))), inference(resolution, [status(thm)], [c_468, c_26])).
% 3.42/1.51  tff(c_649, plain, (![B_12]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_12))) | ~r1_tarski('#skF_5', B_12))), inference(resolution, [status(thm)], [c_20, c_635])).
% 3.42/1.51  tff(c_854, plain, (![A_172, B_173, C_174, D_175]: (r2_relset_1(A_172, B_173, C_174, C_174) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.42/1.51  tff(c_879, plain, (![C_176]: (r2_relset_1('#skF_4', '#skF_5', C_176, C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_54, c_854])).
% 3.42/1.51  tff(c_882, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_7') | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_649, c_879])).
% 3.42/1.51  tff(c_899, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_882])).
% 3.42/1.51  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_802, c_899])).
% 3.42/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.51  
% 3.42/1.51  Inference rules
% 3.42/1.51  ----------------------
% 3.42/1.51  #Ref     : 0
% 3.42/1.51  #Sup     : 186
% 3.42/1.51  #Fact    : 0
% 3.42/1.51  #Define  : 0
% 3.42/1.51  #Split   : 5
% 3.42/1.51  #Chain   : 0
% 3.42/1.51  #Close   : 0
% 3.42/1.51  
% 3.42/1.51  Ordering : KBO
% 3.42/1.51  
% 3.42/1.51  Simplification rules
% 3.42/1.51  ----------------------
% 3.42/1.51  #Subsume      : 24
% 3.42/1.51  #Demod        : 51
% 3.42/1.51  #Tautology    : 42
% 3.42/1.51  #SimpNegUnit  : 3
% 3.42/1.51  #BackRed      : 1
% 3.42/1.51  
% 3.42/1.51  #Partial instantiations: 0
% 3.42/1.51  #Strategies tried      : 1
% 3.42/1.51  
% 3.42/1.51  Timing (in seconds)
% 3.42/1.51  ----------------------
% 3.42/1.52  Preprocessing        : 0.33
% 3.42/1.52  Parsing              : 0.17
% 3.42/1.52  CNF conversion       : 0.03
% 3.42/1.52  Main loop            : 0.41
% 3.42/1.52  Inferencing          : 0.16
% 3.42/1.52  Reduction            : 0.11
% 3.42/1.52  Demodulation         : 0.08
% 3.42/1.52  BG Simplification    : 0.02
% 3.42/1.52  Subsumption          : 0.08
% 3.42/1.52  Abstraction          : 0.02
% 3.42/1.52  MUC search           : 0.00
% 3.42/1.52  Cooper               : 0.00
% 3.42/1.52  Total                : 0.78
% 3.42/1.52  Index Insertion      : 0.00
% 3.42/1.52  Index Deletion       : 0.00
% 3.42/1.52  Index Matching       : 0.00
% 3.42/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
