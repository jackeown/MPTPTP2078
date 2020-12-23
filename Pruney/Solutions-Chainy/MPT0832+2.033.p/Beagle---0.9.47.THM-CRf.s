%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:44 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   67 (  99 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 153 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_42])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_11,B_12)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k8_relat_1(A_13,B_14),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_32])).

tff(c_73,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_49,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_88,plain,(
    ! [A_49] :
      ( v1_relat_1(A_49)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_49,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83,c_49])).

tff(c_93,plain,(
    ! [A_50] :
      ( v1_relat_1(A_50)
      | ~ r1_tarski(A_50,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_88])).

tff(c_101,plain,(
    ! [A_13] :
      ( v1_relat_1(k8_relat_1(A_13,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_105,plain,(
    ! [A_13] : v1_relat_1(k8_relat_1(A_13,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_101])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_15,B_16)),k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_157,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_166,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_157])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( m1_subset_1(k1_relset_1(A_17,B_18,C_19),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_184,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_18])).

tff(c_188,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_184])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_197,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_188,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_209,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,'#skF_3')
      | ~ r1_tarski(A_73,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_213,plain,(
    ! [A_15] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_15,'#skF_4')),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_209])).

tff(c_224,plain,(
    ! [A_15] : r1_tarski(k1_relat_1(k8_relat_1(A_15,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_213])).

tff(c_307,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ r1_tarski(k2_relat_1(C_85),B_87)
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_239,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k6_relset_1(A_75,B_76,C_77,D_78) = k8_relat_1(C_77,D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_250,plain,(
    ! [C_77] : k6_relset_1('#skF_3','#skF_1',C_77,'#skF_4') = k8_relat_1(C_77,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_26,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_252,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_26])).

tff(c_310,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_307,c_252])).

tff(c_324,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_224,c_310])).

tff(c_333,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_324])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.31  
% 2.35/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.32  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.32  
% 2.35/1.32  %Foreground sorts:
% 2.35/1.32  
% 2.35/1.32  
% 2.35/1.32  %Background operators:
% 2.35/1.32  
% 2.35/1.32  
% 2.35/1.32  %Foreground operators:
% 2.35/1.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.35/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.32  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.35/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.35/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.32  
% 2.35/1.33  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.33  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.35/1.33  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.35/1.33  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.35/1.33  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.35/1.33  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.35/1.33  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.35/1.33  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_wellord1)).
% 2.35/1.33  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.35/1.33  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.35/1.33  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.35/1.33  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.35/1.33  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.33  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.33  tff(c_42, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.33  tff(c_48, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_42])).
% 2.35/1.33  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 2.35/1.33  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k2_relat_1(k8_relat_1(A_11, B_12)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.35/1.33  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k8_relat_1(A_13, B_14), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.35/1.33  tff(c_32, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.33  tff(c_40, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_32])).
% 2.35/1.33  tff(c_73, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.33  tff(c_83, plain, (![A_49]: (r1_tarski(A_49, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_49, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_73])).
% 2.35/1.33  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.33  tff(c_49, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.35/1.33  tff(c_88, plain, (![A_49]: (v1_relat_1(A_49) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_49, '#skF_4'))), inference(resolution, [status(thm)], [c_83, c_49])).
% 2.35/1.33  tff(c_93, plain, (![A_50]: (v1_relat_1(A_50) | ~r1_tarski(A_50, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_88])).
% 2.35/1.33  tff(c_101, plain, (![A_13]: (v1_relat_1(k8_relat_1(A_13, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_93])).
% 2.35/1.33  tff(c_105, plain, (![A_13]: (v1_relat_1(k8_relat_1(A_13, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_101])).
% 2.35/1.33  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k1_relat_1(k8_relat_1(A_15, B_16)), k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.33  tff(c_157, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.35/1.33  tff(c_166, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_157])).
% 2.35/1.33  tff(c_18, plain, (![A_17, B_18, C_19]: (m1_subset_1(k1_relset_1(A_17, B_18, C_19), k1_zfmisc_1(A_17)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.33  tff(c_184, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_166, c_18])).
% 2.35/1.33  tff(c_188, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_184])).
% 2.35/1.33  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.33  tff(c_197, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_188, c_4])).
% 2.35/1.33  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.33  tff(c_209, plain, (![A_73]: (r1_tarski(A_73, '#skF_3') | ~r1_tarski(A_73, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_197, c_2])).
% 2.35/1.33  tff(c_213, plain, (![A_15]: (r1_tarski(k1_relat_1(k8_relat_1(A_15, '#skF_4')), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_209])).
% 2.35/1.33  tff(c_224, plain, (![A_15]: (r1_tarski(k1_relat_1(k8_relat_1(A_15, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_213])).
% 2.35/1.33  tff(c_307, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~r1_tarski(k2_relat_1(C_85), B_87) | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.35/1.33  tff(c_239, plain, (![A_75, B_76, C_77, D_78]: (k6_relset_1(A_75, B_76, C_77, D_78)=k8_relat_1(C_77, D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.35/1.33  tff(c_250, plain, (![C_77]: (k6_relset_1('#skF_3', '#skF_1', C_77, '#skF_4')=k8_relat_1(C_77, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_239])).
% 2.35/1.33  tff(c_26, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.35/1.33  tff(c_252, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_26])).
% 2.35/1.33  tff(c_310, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_307, c_252])).
% 2.35/1.33  tff(c_324, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_224, c_310])).
% 2.35/1.33  tff(c_333, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_324])).
% 2.35/1.33  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_333])).
% 2.35/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  Inference rules
% 2.35/1.33  ----------------------
% 2.35/1.33  #Ref     : 0
% 2.35/1.33  #Sup     : 66
% 2.35/1.33  #Fact    : 0
% 2.35/1.33  #Define  : 0
% 2.35/1.33  #Split   : 3
% 2.35/1.33  #Chain   : 0
% 2.35/1.33  #Close   : 0
% 2.35/1.33  
% 2.35/1.33  Ordering : KBO
% 2.35/1.33  
% 2.35/1.33  Simplification rules
% 2.35/1.33  ----------------------
% 2.35/1.33  #Subsume      : 8
% 2.35/1.33  #Demod        : 15
% 2.35/1.33  #Tautology    : 8
% 2.35/1.33  #SimpNegUnit  : 0
% 2.35/1.33  #BackRed      : 2
% 2.35/1.33  
% 2.35/1.33  #Partial instantiations: 0
% 2.35/1.33  #Strategies tried      : 1
% 2.35/1.33  
% 2.35/1.33  Timing (in seconds)
% 2.35/1.33  ----------------------
% 2.35/1.34  Preprocessing        : 0.31
% 2.35/1.34  Parsing              : 0.17
% 2.35/1.34  CNF conversion       : 0.02
% 2.35/1.34  Main loop            : 0.25
% 2.35/1.34  Inferencing          : 0.09
% 2.35/1.34  Reduction            : 0.07
% 2.35/1.34  Demodulation         : 0.05
% 2.35/1.34  BG Simplification    : 0.01
% 2.35/1.34  Subsumption          : 0.05
% 2.35/1.34  Abstraction          : 0.01
% 2.35/1.34  MUC search           : 0.00
% 2.35/1.34  Cooper               : 0.00
% 2.35/1.34  Total                : 0.60
% 2.35/1.34  Index Insertion      : 0.00
% 2.35/1.34  Index Deletion       : 0.00
% 2.35/1.34  Index Matching       : 0.00
% 2.35/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
