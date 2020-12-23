%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:41 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 154 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 261 expanded)
%              Number of equality atoms :   10 (  13 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_35,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_97,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_50,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_97])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_221,plain,(
    ! [A_67,A_68] :
      ( r1_tarski(A_67,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_67,A_68)
      | ~ r1_tarski(A_68,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_110,c_8])).

tff(c_239,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(B_11,'#skF_4')
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_221])).

tff(c_106,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_47,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_97])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_121,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_295,plain,(
    ! [A_79,B_80,A_81] :
      ( k1_relset_1(A_79,B_80,A_81) = k1_relat_1(A_81)
      | ~ r1_tarski(A_81,k2_zfmisc_1(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_322,plain,(
    ! [A_82] :
      ( k1_relset_1('#skF_3','#skF_1',A_82) = k1_relat_1(A_82)
      | ~ r1_tarski(A_82,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_106,c_295])).

tff(c_330,plain,(
    ! [A_10] :
      ( k1_relset_1('#skF_3','#skF_1',k8_relat_1(A_10,'#skF_4')) = k1_relat_1(k8_relat_1(A_10,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_322])).

tff(c_338,plain,(
    ! [A_10] : k1_relset_1('#skF_3','#skF_1',k8_relat_1(A_10,'#skF_4')) = k1_relat_1(k8_relat_1(A_10,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_330])).

tff(c_174,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k1_relset_1(A_63,B_64,C_65),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_405,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski(k1_relset_1(A_94,B_95,C_96),A_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(resolution,[status(thm)],[c_174,c_10])).

tff(c_421,plain,(
    ! [A_97,B_98,A_99] :
      ( r1_tarski(k1_relset_1(A_97,B_98,A_99),A_97)
      | ~ r1_tarski(A_99,k2_zfmisc_1(A_97,B_98)) ) ),
    inference(resolution,[status(thm)],[c_12,c_405])).

tff(c_2199,plain,(
    ! [A_286] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_286,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k8_relat_1(A_286,'#skF_4'),k2_zfmisc_1('#skF_3','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_421])).

tff(c_69,plain,(
    ! [A_6,A_40,B_41] :
      ( v1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_40,B_41)) ) ),
    inference(resolution,[status(thm)],[c_12,c_61])).

tff(c_131,plain,(
    ! [A_54] :
      ( v1_relat_1(A_54)
      | ~ r1_tarski(A_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_110,c_69])).

tff(c_139,plain,(
    ! [A_10] :
      ( v1_relat_1(k8_relat_1(A_10,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_131])).

tff(c_147,plain,(
    ! [A_10] : v1_relat_1(k8_relat_1(A_10,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_139])).

tff(c_341,plain,(
    ! [C_83,A_84,B_85] :
      ( m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ r1_tarski(k2_relat_1(C_83),B_85)
      | ~ r1_tarski(k1_relat_1(C_83),A_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_253,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k6_relset_1(A_70,B_71,C_72,D_73) = k8_relat_1(C_72,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_264,plain,(
    ! [C_72] : k6_relset_1('#skF_3','#skF_1',C_72,'#skF_4') = k8_relat_1(C_72,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_253])).

tff(c_28,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_266,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_28])).

tff(c_344,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_341,c_266])).

tff(c_358,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_344])).

tff(c_403,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_2224,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2199,c_403])).

tff(c_2230,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_239,c_2224])).

tff(c_2237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6,c_2230])).

tff(c_2238,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_2243,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_2238])).

tff(c_2247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.98  
% 4.72/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.98  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.72/1.98  
% 4.72/1.98  %Foreground sorts:
% 4.72/1.98  
% 4.72/1.98  
% 4.72/1.98  %Background operators:
% 4.72/1.98  
% 4.72/1.98  
% 4.72/1.98  %Foreground operators:
% 4.72/1.98  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.72/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.72/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.72/1.98  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 4.72/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.72/1.98  tff('#skF_1', type, '#skF_1': $i).
% 4.72/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.72/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.72/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.72/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.72/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.98  
% 5.03/2.00  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 5.03/2.00  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.03/2.00  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 5.03/2.00  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.03/2.00  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 5.03/2.00  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.03/2.00  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.03/2.00  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.03/2.00  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.03/2.00  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.03/2.00  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 5.03/2.00  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.03/2.00  tff(c_61, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.03/2.00  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_61])).
% 5.03/2.00  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.03/2.00  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.03/2.00  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.03/2.00  tff(c_35, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.03/2.00  tff(c_43, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_35])).
% 5.03/2.00  tff(c_97, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.03/2.00  tff(c_110, plain, (![A_50]: (r1_tarski(A_50, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_50, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_97])).
% 5.03/2.00  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.03/2.00  tff(c_221, plain, (![A_67, A_68]: (r1_tarski(A_67, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_67, A_68) | ~r1_tarski(A_68, '#skF_4'))), inference(resolution, [status(thm)], [c_110, c_8])).
% 5.03/2.00  tff(c_239, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(B_11, '#skF_4') | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_16, c_221])).
% 5.03/2.00  tff(c_106, plain, (![A_47]: (r1_tarski(A_47, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_47, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_97])).
% 5.03/2.00  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.03/2.00  tff(c_121, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.03/2.00  tff(c_295, plain, (![A_79, B_80, A_81]: (k1_relset_1(A_79, B_80, A_81)=k1_relat_1(A_81) | ~r1_tarski(A_81, k2_zfmisc_1(A_79, B_80)))), inference(resolution, [status(thm)], [c_12, c_121])).
% 5.03/2.00  tff(c_322, plain, (![A_82]: (k1_relset_1('#skF_3', '#skF_1', A_82)=k1_relat_1(A_82) | ~r1_tarski(A_82, '#skF_4'))), inference(resolution, [status(thm)], [c_106, c_295])).
% 5.03/2.00  tff(c_330, plain, (![A_10]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(A_10, '#skF_4'))=k1_relat_1(k8_relat_1(A_10, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_322])).
% 5.03/2.00  tff(c_338, plain, (![A_10]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(A_10, '#skF_4'))=k1_relat_1(k8_relat_1(A_10, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_330])).
% 5.03/2.00  tff(c_174, plain, (![A_63, B_64, C_65]: (m1_subset_1(k1_relset_1(A_63, B_64, C_65), k1_zfmisc_1(A_63)) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.03/2.00  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.03/2.00  tff(c_405, plain, (![A_94, B_95, C_96]: (r1_tarski(k1_relset_1(A_94, B_95, C_96), A_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(resolution, [status(thm)], [c_174, c_10])).
% 5.03/2.00  tff(c_421, plain, (![A_97, B_98, A_99]: (r1_tarski(k1_relset_1(A_97, B_98, A_99), A_97) | ~r1_tarski(A_99, k2_zfmisc_1(A_97, B_98)))), inference(resolution, [status(thm)], [c_12, c_405])).
% 5.03/2.00  tff(c_2199, plain, (![A_286]: (r1_tarski(k1_relat_1(k8_relat_1(A_286, '#skF_4')), '#skF_3') | ~r1_tarski(k8_relat_1(A_286, '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_338, c_421])).
% 5.03/2.00  tff(c_69, plain, (![A_6, A_40, B_41]: (v1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_40, B_41)))), inference(resolution, [status(thm)], [c_12, c_61])).
% 5.03/2.00  tff(c_131, plain, (![A_54]: (v1_relat_1(A_54) | ~r1_tarski(A_54, '#skF_4'))), inference(resolution, [status(thm)], [c_110, c_69])).
% 5.03/2.00  tff(c_139, plain, (![A_10]: (v1_relat_1(k8_relat_1(A_10, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_131])).
% 5.03/2.00  tff(c_147, plain, (![A_10]: (v1_relat_1(k8_relat_1(A_10, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_139])).
% 5.03/2.00  tff(c_341, plain, (![C_83, A_84, B_85]: (m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~r1_tarski(k2_relat_1(C_83), B_85) | ~r1_tarski(k1_relat_1(C_83), A_84) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.03/2.00  tff(c_253, plain, (![A_70, B_71, C_72, D_73]: (k6_relset_1(A_70, B_71, C_72, D_73)=k8_relat_1(C_72, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.03/2.00  tff(c_264, plain, (![C_72]: (k6_relset_1('#skF_3', '#skF_1', C_72, '#skF_4')=k8_relat_1(C_72, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_253])).
% 5.03/2.00  tff(c_28, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.03/2.00  tff(c_266, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_28])).
% 5.03/2.00  tff(c_344, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_341, c_266])).
% 5.03/2.00  tff(c_358, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_344])).
% 5.03/2.00  tff(c_403, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_358])).
% 5.03/2.00  tff(c_2224, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_2199, c_403])).
% 5.03/2.00  tff(c_2230, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_239, c_2224])).
% 5.03/2.00  tff(c_2237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_6, c_2230])).
% 5.03/2.00  tff(c_2238, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_358])).
% 5.03/2.00  tff(c_2243, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_2238])).
% 5.03/2.00  tff(c_2247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2243])).
% 5.03/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.03/2.00  
% 5.03/2.00  Inference rules
% 5.03/2.00  ----------------------
% 5.03/2.00  #Ref     : 0
% 5.03/2.00  #Sup     : 475
% 5.03/2.00  #Fact    : 0
% 5.03/2.00  #Define  : 0
% 5.03/2.00  #Split   : 6
% 5.03/2.00  #Chain   : 0
% 5.03/2.00  #Close   : 0
% 5.03/2.00  
% 5.03/2.00  Ordering : KBO
% 5.03/2.00  
% 5.03/2.00  Simplification rules
% 5.03/2.00  ----------------------
% 5.03/2.00  #Subsume      : 28
% 5.03/2.00  #Demod        : 122
% 5.03/2.00  #Tautology    : 58
% 5.03/2.00  #SimpNegUnit  : 0
% 5.03/2.00  #BackRed      : 2
% 5.03/2.00  
% 5.03/2.00  #Partial instantiations: 0
% 5.03/2.00  #Strategies tried      : 1
% 5.03/2.00  
% 5.03/2.00  Timing (in seconds)
% 5.03/2.00  ----------------------
% 5.03/2.01  Preprocessing        : 0.35
% 5.03/2.01  Parsing              : 0.18
% 5.03/2.01  CNF conversion       : 0.02
% 5.03/2.01  Main loop            : 0.80
% 5.03/2.01  Inferencing          : 0.28
% 5.03/2.01  Reduction            : 0.24
% 5.03/2.01  Demodulation         : 0.17
% 5.03/2.01  BG Simplification    : 0.04
% 5.03/2.01  Subsumption          : 0.18
% 5.03/2.01  Abstraction          : 0.05
% 5.03/2.01  MUC search           : 0.00
% 5.03/2.01  Cooper               : 0.00
% 5.03/2.01  Total                : 1.19
% 5.03/2.01  Index Insertion      : 0.00
% 5.03/2.01  Index Deletion       : 0.00
% 5.03/2.01  Index Matching       : 0.00
% 5.03/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
