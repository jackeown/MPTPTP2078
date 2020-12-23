%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:44 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 129 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 219 expanded)
%              Number of equality atoms :    8 (  14 expanded)
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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_46])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_191,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( m1_subset_1(A_67,k1_zfmisc_1(k2_zfmisc_1(B_68,C_69)))
      | ~ r1_tarski(A_67,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(B_68,C_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_387,plain,(
    ! [A_109,B_110,B_111,C_112] :
      ( m1_subset_1(k8_relat_1(A_109,B_110),k1_zfmisc_1(k2_zfmisc_1(B_111,C_112)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(B_111,C_112)))
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_12,c_191])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_relset_1(A_15,B_16,C_17) = k1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1102,plain,(
    ! [B_274,C_275,A_276,B_277] :
      ( k1_relset_1(B_274,C_275,k8_relat_1(A_276,B_277)) = k1_relat_1(k8_relat_1(A_276,B_277))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_zfmisc_1(B_274,C_275)))
      | ~ v1_relat_1(B_277) ) ),
    inference(resolution,[status(thm)],[c_387,c_16])).

tff(c_1118,plain,(
    ! [A_276] :
      ( k1_relset_1('#skF_3','#skF_1',k8_relat_1(A_276,'#skF_4')) = k1_relat_1(k8_relat_1(A_276,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1102])).

tff(c_1128,plain,(
    ! [A_278] : k1_relset_1('#skF_3','#skF_1',k8_relat_1(A_278,'#skF_4')) = k1_relat_1(k8_relat_1(A_278,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1118])).

tff(c_82,plain,(
    ! [A_50,B_51,C_52] :
      ( m1_subset_1(k1_relset_1(A_50,B_51,C_52),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(k1_relset_1(A_50,B_51,C_52),A_50)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_412,plain,(
    ! [B_111,C_112,A_109,B_110] :
      ( r1_tarski(k1_relset_1(B_111,C_112,k8_relat_1(A_109,B_110)),B_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(B_111,C_112)))
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_387,c_95])).

tff(c_1140,plain,(
    ! [A_278] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_278,'#skF_4')),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1128,c_412])).

tff(c_1154,plain,(
    ! [A_278] : r1_tarski(k1_relat_1(k8_relat_1(A_278,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26,c_1140])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(A_41)
      | ~ v1_relat_1(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_69,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k8_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_55])).

tff(c_291,plain,(
    ! [C_86,A_87,B_88] :
      ( m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ r1_tarski(k2_relat_1(C_86),B_88)
      | ~ r1_tarski(k1_relat_1(C_86),A_87)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_164,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k6_relset_1(A_62,B_63,C_64,D_65) = k8_relat_1(C_64,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_175,plain,(
    ! [C_64] : k6_relset_1('#skF_3','#skF_1',C_64,'#skF_4') = k8_relat_1(C_64,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_164])).

tff(c_24,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_177,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_24])).

tff(c_312,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_291,c_177])).

tff(c_367,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_370,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_367])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_370])).

tff(c_375,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_377,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_380,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_377])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_380])).

tff(c_385,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_1158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  
% 3.44/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.44/1.59  
% 3.44/1.59  %Foreground sorts:
% 3.44/1.59  
% 3.44/1.59  
% 3.44/1.59  %Background operators:
% 3.44/1.59  
% 3.44/1.59  
% 3.44/1.59  %Foreground operators:
% 3.44/1.59  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.59  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 3.44/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.44/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.59  
% 3.44/1.61  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.44/1.61  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 3.44/1.61  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.44/1.61  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 3.44/1.61  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 3.44/1.61  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.44/1.61  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.44/1.61  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.44/1.61  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 3.44/1.61  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.44/1.61  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 3.44/1.61  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.61  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.61  tff(c_40, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.61  tff(c_46, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_40])).
% 3.44/1.61  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 3.44/1.61  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.44/1.61  tff(c_191, plain, (![A_67, B_68, C_69, D_70]: (m1_subset_1(A_67, k1_zfmisc_1(k2_zfmisc_1(B_68, C_69))) | ~r1_tarski(A_67, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(B_68, C_69))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.44/1.61  tff(c_387, plain, (![A_109, B_110, B_111, C_112]: (m1_subset_1(k8_relat_1(A_109, B_110), k1_zfmisc_1(k2_zfmisc_1(B_111, C_112))) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(B_111, C_112))) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_12, c_191])).
% 3.44/1.61  tff(c_16, plain, (![A_15, B_16, C_17]: (k1_relset_1(A_15, B_16, C_17)=k1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.61  tff(c_1102, plain, (![B_274, C_275, A_276, B_277]: (k1_relset_1(B_274, C_275, k8_relat_1(A_276, B_277))=k1_relat_1(k8_relat_1(A_276, B_277)) | ~m1_subset_1(B_277, k1_zfmisc_1(k2_zfmisc_1(B_274, C_275))) | ~v1_relat_1(B_277))), inference(resolution, [status(thm)], [c_387, c_16])).
% 3.44/1.61  tff(c_1118, plain, (![A_276]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(A_276, '#skF_4'))=k1_relat_1(k8_relat_1(A_276, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1102])).
% 3.44/1.61  tff(c_1128, plain, (![A_278]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(A_278, '#skF_4'))=k1_relat_1(k8_relat_1(A_278, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1118])).
% 3.44/1.61  tff(c_82, plain, (![A_50, B_51, C_52]: (m1_subset_1(k1_relset_1(A_50, B_51, C_52), k1_zfmisc_1(A_50)) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.61  tff(c_95, plain, (![A_50, B_51, C_52]: (r1_tarski(k1_relset_1(A_50, B_51, C_52), A_50) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(resolution, [status(thm)], [c_82, c_2])).
% 3.44/1.61  tff(c_412, plain, (![B_111, C_112, A_109, B_110]: (r1_tarski(k1_relset_1(B_111, C_112, k8_relat_1(A_109, B_110)), B_111) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(B_111, C_112))) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_387, c_95])).
% 3.44/1.61  tff(c_1140, plain, (![A_278]: (r1_tarski(k1_relat_1(k8_relat_1(A_278, '#skF_4')), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1128, c_412])).
% 3.44/1.61  tff(c_1154, plain, (![A_278]: (r1_tarski(k1_relat_1(k8_relat_1(A_278, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_26, c_1140])).
% 3.44/1.61  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.61  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.61  tff(c_55, plain, (![A_41, B_42]: (v1_relat_1(A_41) | ~v1_relat_1(B_42) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_4, c_40])).
% 3.44/1.61  tff(c_69, plain, (![A_10, B_11]: (v1_relat_1(k8_relat_1(A_10, B_11)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_12, c_55])).
% 3.44/1.61  tff(c_291, plain, (![C_86, A_87, B_88]: (m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~r1_tarski(k2_relat_1(C_86), B_88) | ~r1_tarski(k1_relat_1(C_86), A_87) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.44/1.61  tff(c_164, plain, (![A_62, B_63, C_64, D_65]: (k6_relset_1(A_62, B_63, C_64, D_65)=k8_relat_1(C_64, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.61  tff(c_175, plain, (![C_64]: (k6_relset_1('#skF_3', '#skF_1', C_64, '#skF_4')=k8_relat_1(C_64, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_164])).
% 3.44/1.61  tff(c_24, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.61  tff(c_177, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_24])).
% 3.44/1.61  tff(c_312, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_291, c_177])).
% 3.44/1.61  tff(c_367, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_312])).
% 3.44/1.61  tff(c_370, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_69, c_367])).
% 3.44/1.61  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_370])).
% 3.44/1.61  tff(c_375, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_312])).
% 3.44/1.61  tff(c_377, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_375])).
% 3.44/1.61  tff(c_380, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_377])).
% 3.44/1.61  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_380])).
% 3.44/1.61  tff(c_385, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_375])).
% 3.44/1.61  tff(c_1158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1154, c_385])).
% 3.44/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  
% 3.44/1.61  Inference rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Ref     : 0
% 3.44/1.61  #Sup     : 256
% 3.44/1.61  #Fact    : 0
% 3.44/1.61  #Define  : 0
% 3.44/1.61  #Split   : 6
% 3.44/1.61  #Chain   : 0
% 3.44/1.61  #Close   : 0
% 3.44/1.61  
% 3.44/1.61  Ordering : KBO
% 3.44/1.61  
% 3.44/1.61  Simplification rules
% 3.44/1.61  ----------------------
% 3.44/1.61  #Subsume      : 37
% 3.44/1.61  #Demod        : 62
% 3.44/1.61  #Tautology    : 27
% 3.44/1.61  #SimpNegUnit  : 0
% 3.44/1.61  #BackRed      : 4
% 3.44/1.61  
% 3.44/1.61  #Partial instantiations: 0
% 3.44/1.61  #Strategies tried      : 1
% 3.44/1.61  
% 3.44/1.61  Timing (in seconds)
% 3.44/1.61  ----------------------
% 3.44/1.61  Preprocessing        : 0.30
% 3.44/1.61  Parsing              : 0.17
% 3.44/1.61  CNF conversion       : 0.02
% 3.44/1.61  Main loop            : 0.50
% 3.44/1.61  Inferencing          : 0.19
% 3.44/1.61  Reduction            : 0.14
% 3.44/1.61  Demodulation         : 0.09
% 3.44/1.61  BG Simplification    : 0.02
% 3.75/1.61  Subsumption          : 0.10
% 3.75/1.61  Abstraction          : 0.03
% 3.75/1.61  MUC search           : 0.00
% 3.75/1.61  Cooper               : 0.00
% 3.75/1.61  Total                : 0.83
% 3.75/1.61  Index Insertion      : 0.00
% 3.75/1.61  Index Deletion       : 0.00
% 3.75/1.61  Index Matching       : 0.00
% 3.75/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
