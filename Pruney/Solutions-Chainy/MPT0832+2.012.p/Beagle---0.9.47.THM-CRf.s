%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:41 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 120 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 201 expanded)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_44])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k8_relat_1(A_7,B_8),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( m1_subset_1(A_65,k1_zfmisc_1(k2_zfmisc_1(B_66,C_67)))
      | ~ r1_tarski(A_65,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(B_66,C_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_906,plain,(
    ! [A_168,B_169,B_170,C_171] :
      ( m1_subset_1(k8_relat_1(A_168,B_169),k1_zfmisc_1(k2_zfmisc_1(B_170,C_171)))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_zfmisc_1(B_170,C_171)))
      | ~ v1_relat_1(B_169) ) ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_relset_1(A_15,B_16,C_17) = k1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2353,plain,(
    ! [B_407,C_408,A_409,B_410] :
      ( k1_relset_1(B_407,C_408,k8_relat_1(A_409,B_410)) = k1_relat_1(k8_relat_1(A_409,B_410))
      | ~ m1_subset_1(B_410,k1_zfmisc_1(k2_zfmisc_1(B_407,C_408)))
      | ~ v1_relat_1(B_410) ) ),
    inference(resolution,[status(thm)],[c_906,c_20])).

tff(c_2374,plain,(
    ! [A_409] :
      ( k1_relset_1('#skF_3','#skF_1',k8_relat_1(A_409,'#skF_4')) = k1_relat_1(k8_relat_1(A_409,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_2353])).

tff(c_2390,plain,(
    ! [A_411] : k1_relset_1('#skF_3','#skF_1',k8_relat_1(A_411,'#skF_4')) = k1_relat_1(k8_relat_1(A_411,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2374])).

tff(c_113,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k1_relset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(k1_relset_1(A_54,B_55,C_56),A_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(resolution,[status(thm)],[c_113,c_8])).

tff(c_928,plain,(
    ! [B_170,C_171,A_168,B_169] :
      ( r1_tarski(k1_relset_1(B_170,C_171,k8_relat_1(A_168,B_169)),B_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(k2_zfmisc_1(B_170,C_171)))
      | ~ v1_relat_1(B_169) ) ),
    inference(resolution,[status(thm)],[c_906,c_130])).

tff(c_2396,plain,(
    ! [A_411] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_411,'#skF_4')),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2390,c_928])).

tff(c_2411,plain,(
    ! [A_411] : r1_tarski(k1_relat_1(k8_relat_1(A_411,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_30,c_2396])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_5,B_6)),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_574,plain,(
    ! [A_138,B_139,B_140,C_141] :
      ( m1_subset_1(k8_relat_1(A_138,B_139),k1_zfmisc_1(k2_zfmisc_1(B_140,C_141)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(B_140,C_141)))
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_16,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_639,plain,(
    ! [A_143,B_144,B_145,C_146] :
      ( v1_relat_1(k8_relat_1(A_143,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_zfmisc_1(B_145,C_146)))
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_574,c_16])).

tff(c_653,plain,(
    ! [A_143] :
      ( v1_relat_1(k8_relat_1(A_143,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_639])).

tff(c_663,plain,(
    ! [A_143] : v1_relat_1(k8_relat_1(A_143,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_653])).

tff(c_263,plain,(
    ! [C_82,A_83,B_84] :
      ( m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_144,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k6_relset_1(A_60,B_61,C_62,D_63) = k8_relat_1(C_62,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_155,plain,(
    ! [C_62] : k6_relset_1('#skF_3','#skF_1',C_62,'#skF_4') = k8_relat_1(C_62,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_144])).

tff(c_28,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_157,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_28])).

tff(c_281,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_263,c_157])).

tff(c_400,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_400])).

tff(c_667,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_720,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_723,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_720])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_723])).

tff(c_728,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_2417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2411,c_728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.34/1.99  
% 5.34/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.34/1.99  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.34/1.99  
% 5.34/1.99  %Foreground sorts:
% 5.34/1.99  
% 5.34/1.99  
% 5.34/1.99  %Background operators:
% 5.34/1.99  
% 5.34/1.99  
% 5.34/1.99  %Foreground operators:
% 5.34/1.99  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.34/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.34/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.34/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.34/1.99  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 5.34/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.34/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.34/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.34/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.34/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.34/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.34/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.34/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.34/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.34/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.34/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.34/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.34/1.99  
% 5.34/2.01  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 5.34/2.01  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.34/2.01  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 5.34/2.01  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 5.34/2.01  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.34/2.01  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.34/2.01  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.34/2.01  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 5.34/2.01  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.34/2.01  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 5.34/2.01  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.34/2.01  tff(c_44, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.34/2.01  tff(c_53, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_44])).
% 5.34/2.01  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k8_relat_1(A_7, B_8), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.34/2.01  tff(c_171, plain, (![A_65, B_66, C_67, D_68]: (m1_subset_1(A_65, k1_zfmisc_1(k2_zfmisc_1(B_66, C_67))) | ~r1_tarski(A_65, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(B_66, C_67))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.34/2.01  tff(c_906, plain, (![A_168, B_169, B_170, C_171]: (m1_subset_1(k8_relat_1(A_168, B_169), k1_zfmisc_1(k2_zfmisc_1(B_170, C_171))) | ~m1_subset_1(B_169, k1_zfmisc_1(k2_zfmisc_1(B_170, C_171))) | ~v1_relat_1(B_169))), inference(resolution, [status(thm)], [c_14, c_171])).
% 5.34/2.01  tff(c_20, plain, (![A_15, B_16, C_17]: (k1_relset_1(A_15, B_16, C_17)=k1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.34/2.01  tff(c_2353, plain, (![B_407, C_408, A_409, B_410]: (k1_relset_1(B_407, C_408, k8_relat_1(A_409, B_410))=k1_relat_1(k8_relat_1(A_409, B_410)) | ~m1_subset_1(B_410, k1_zfmisc_1(k2_zfmisc_1(B_407, C_408))) | ~v1_relat_1(B_410))), inference(resolution, [status(thm)], [c_906, c_20])).
% 5.34/2.01  tff(c_2374, plain, (![A_409]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(A_409, '#skF_4'))=k1_relat_1(k8_relat_1(A_409, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_2353])).
% 5.34/2.01  tff(c_2390, plain, (![A_411]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(A_411, '#skF_4'))=k1_relat_1(k8_relat_1(A_411, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2374])).
% 5.34/2.01  tff(c_113, plain, (![A_54, B_55, C_56]: (m1_subset_1(k1_relset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.34/2.01  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.34/2.01  tff(c_130, plain, (![A_54, B_55, C_56]: (r1_tarski(k1_relset_1(A_54, B_55, C_56), A_54) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(resolution, [status(thm)], [c_113, c_8])).
% 5.34/2.01  tff(c_928, plain, (![B_170, C_171, A_168, B_169]: (r1_tarski(k1_relset_1(B_170, C_171, k8_relat_1(A_168, B_169)), B_170) | ~m1_subset_1(B_169, k1_zfmisc_1(k2_zfmisc_1(B_170, C_171))) | ~v1_relat_1(B_169))), inference(resolution, [status(thm)], [c_906, c_130])).
% 5.34/2.01  tff(c_2396, plain, (![A_411]: (r1_tarski(k1_relat_1(k8_relat_1(A_411, '#skF_4')), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2390, c_928])).
% 5.34/2.01  tff(c_2411, plain, (![A_411]: (r1_tarski(k1_relat_1(k8_relat_1(A_411, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_30, c_2396])).
% 5.34/2.01  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k2_relat_1(k8_relat_1(A_5, B_6)), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.34/2.01  tff(c_574, plain, (![A_138, B_139, B_140, C_141]: (m1_subset_1(k8_relat_1(A_138, B_139), k1_zfmisc_1(k2_zfmisc_1(B_140, C_141))) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(B_140, C_141))) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_14, c_171])).
% 5.34/2.01  tff(c_16, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.34/2.01  tff(c_639, plain, (![A_143, B_144, B_145, C_146]: (v1_relat_1(k8_relat_1(A_143, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_zfmisc_1(B_145, C_146))) | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_574, c_16])).
% 5.34/2.01  tff(c_653, plain, (![A_143]: (v1_relat_1(k8_relat_1(A_143, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_639])).
% 5.34/2.01  tff(c_663, plain, (![A_143]: (v1_relat_1(k8_relat_1(A_143, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_653])).
% 5.34/2.01  tff(c_263, plain, (![C_82, A_83, B_84]: (m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.34/2.01  tff(c_144, plain, (![A_60, B_61, C_62, D_63]: (k6_relset_1(A_60, B_61, C_62, D_63)=k8_relat_1(C_62, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.34/2.01  tff(c_155, plain, (![C_62]: (k6_relset_1('#skF_3', '#skF_1', C_62, '#skF_4')=k8_relat_1(C_62, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_144])).
% 5.34/2.01  tff(c_28, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.34/2.01  tff(c_157, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_28])).
% 5.34/2.01  tff(c_281, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_263, c_157])).
% 5.34/2.01  tff(c_400, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_281])).
% 5.34/2.01  tff(c_666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_663, c_400])).
% 5.34/2.01  tff(c_667, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_281])).
% 5.34/2.01  tff(c_720, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_667])).
% 5.34/2.01  tff(c_723, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_720])).
% 5.34/2.01  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_723])).
% 5.34/2.01  tff(c_728, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_667])).
% 5.34/2.01  tff(c_2417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2411, c_728])).
% 5.34/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.34/2.01  
% 5.34/2.01  Inference rules
% 5.34/2.01  ----------------------
% 5.34/2.01  #Ref     : 0
% 5.34/2.01  #Sup     : 544
% 5.34/2.01  #Fact    : 0
% 5.34/2.01  #Define  : 0
% 5.34/2.01  #Split   : 12
% 5.34/2.01  #Chain   : 0
% 5.34/2.01  #Close   : 0
% 5.34/2.01  
% 5.34/2.01  Ordering : KBO
% 5.34/2.01  
% 5.34/2.01  Simplification rules
% 5.34/2.01  ----------------------
% 5.34/2.01  #Subsume      : 45
% 5.34/2.01  #Demod        : 191
% 5.34/2.01  #Tautology    : 131
% 5.34/2.01  #SimpNegUnit  : 0
% 5.34/2.01  #BackRed      : 5
% 5.34/2.01  
% 5.34/2.01  #Partial instantiations: 0
% 5.34/2.01  #Strategies tried      : 1
% 5.34/2.01  
% 5.34/2.01  Timing (in seconds)
% 5.34/2.01  ----------------------
% 5.34/2.01  Preprocessing        : 0.32
% 5.34/2.01  Parsing              : 0.17
% 5.34/2.01  CNF conversion       : 0.02
% 5.34/2.01  Main loop            : 0.92
% 5.34/2.01  Inferencing          : 0.33
% 5.34/2.01  Reduction            : 0.28
% 5.34/2.01  Demodulation         : 0.20
% 5.34/2.01  BG Simplification    : 0.04
% 5.34/2.01  Subsumption          : 0.20
% 5.34/2.01  Abstraction          : 0.05
% 5.34/2.01  MUC search           : 0.00
% 5.34/2.01  Cooper               : 0.00
% 5.34/2.01  Total                : 1.27
% 5.34/2.01  Index Insertion      : 0.00
% 5.34/2.01  Index Deletion       : 0.00
% 5.34/2.01  Index Matching       : 0.00
% 5.34/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
