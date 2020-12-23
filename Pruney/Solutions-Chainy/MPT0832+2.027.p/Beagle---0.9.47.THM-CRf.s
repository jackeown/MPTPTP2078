%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:43 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 157 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 256 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_38,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_33,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_11,B_12)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k8_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_87,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_51,B_52)),k1_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_50,plain,(
    ! [B_45,A_46] :
      ( k7_relat_1(B_45,A_46) = B_45
      | ~ v4_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_56,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_53])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_14])).

tff(c_64,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_60])).

tff(c_66,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,'#skF_3')
      | ~ r1_tarski(A_47,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_66])).

tff(c_91,plain,(
    ! [A_51] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_51,'#skF_4')),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_87,c_73])).

tff(c_96,plain,(
    ! [A_51] : r1_tarski(k1_relat_1(k8_relat_1(A_51,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_91])).

tff(c_310,plain,(
    ! [C_88,A_89,B_90] :
      ( m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ r1_tarski(k2_relat_1(C_88),B_90)
      | ~ r1_tarski(k1_relat_1(C_88),A_89)
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k6_relset_1(A_66,B_67,C_68,D_69) = k8_relat_1(C_68,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_165,plain,(
    ! [C_68] : k6_relset_1('#skF_3','#skF_1',C_68,'#skF_4') = k8_relat_1(C_68,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_26,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_166,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_26])).

tff(c_313,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_310,c_166])).

tff(c_327,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_313])).

tff(c_334,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_337,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_334])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_337])).

tff(c_342,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_346,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_342])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:23:14 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.32  
% 2.42/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.32  
% 2.42/1.32  %Foreground sorts:
% 2.42/1.32  
% 2.42/1.32  
% 2.42/1.32  %Background operators:
% 2.42/1.32  
% 2.42/1.32  
% 2.42/1.32  %Foreground operators:
% 2.42/1.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.32  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.42/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.42/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.42/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.32  
% 2.42/1.34  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.42/1.34  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.42/1.34  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.42/1.34  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.42/1.34  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.42/1.34  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_wellord1)).
% 2.42/1.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.42/1.34  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.42/1.34  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.42/1.34  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.42/1.34  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.42/1.34  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.42/1.34  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.34  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.42/1.34  tff(c_33, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.34  tff(c_36, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_33])).
% 2.42/1.34  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 2.42/1.34  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(k2_relat_1(k8_relat_1(A_11, B_12)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.42/1.34  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k8_relat_1(A_7, B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.42/1.34  tff(c_87, plain, (![A_51, B_52]: (r1_tarski(k1_relat_1(k8_relat_1(A_51, B_52)), k1_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.42/1.34  tff(c_40, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.34  tff(c_44, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.42/1.34  tff(c_50, plain, (![B_45, A_46]: (k7_relat_1(B_45, A_46)=B_45 | ~v4_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.34  tff(c_53, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_50])).
% 2.42/1.34  tff(c_56, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39, c_53])).
% 2.42/1.34  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.42/1.34  tff(c_60, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_56, c_14])).
% 2.42/1.34  tff(c_64, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_60])).
% 2.42/1.34  tff(c_66, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.34  tff(c_73, plain, (![A_47]: (r1_tarski(A_47, '#skF_3') | ~r1_tarski(A_47, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_66])).
% 2.42/1.34  tff(c_91, plain, (![A_51]: (r1_tarski(k1_relat_1(k8_relat_1(A_51, '#skF_4')), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_87, c_73])).
% 2.42/1.34  tff(c_96, plain, (![A_51]: (r1_tarski(k1_relat_1(k8_relat_1(A_51, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_91])).
% 2.42/1.34  tff(c_310, plain, (![C_88, A_89, B_90]: (m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~r1_tarski(k2_relat_1(C_88), B_90) | ~r1_tarski(k1_relat_1(C_88), A_89) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.42/1.34  tff(c_162, plain, (![A_66, B_67, C_68, D_69]: (k6_relset_1(A_66, B_67, C_68, D_69)=k8_relat_1(C_68, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.42/1.34  tff(c_165, plain, (![C_68]: (k6_relset_1('#skF_3', '#skF_1', C_68, '#skF_4')=k8_relat_1(C_68, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_162])).
% 2.42/1.34  tff(c_26, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.42/1.34  tff(c_166, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_26])).
% 2.42/1.34  tff(c_313, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_310, c_166])).
% 2.42/1.34  tff(c_327, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_313])).
% 2.42/1.34  tff(c_334, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_327])).
% 2.42/1.34  tff(c_337, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_334])).
% 2.42/1.34  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_337])).
% 2.42/1.34  tff(c_342, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_327])).
% 2.42/1.34  tff(c_346, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_342])).
% 2.42/1.34  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_346])).
% 2.42/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  Inference rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Ref     : 0
% 2.42/1.34  #Sup     : 64
% 2.42/1.34  #Fact    : 0
% 2.42/1.34  #Define  : 0
% 2.42/1.34  #Split   : 1
% 2.42/1.34  #Chain   : 0
% 2.42/1.34  #Close   : 0
% 2.42/1.34  
% 2.42/1.34  Ordering : KBO
% 2.42/1.34  
% 2.42/1.34  Simplification rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Subsume      : 2
% 2.42/1.34  #Demod        : 11
% 2.42/1.34  #Tautology    : 5
% 2.42/1.34  #SimpNegUnit  : 0
% 2.42/1.34  #BackRed      : 1
% 2.42/1.34  
% 2.42/1.34  #Partial instantiations: 0
% 2.42/1.34  #Strategies tried      : 1
% 2.42/1.34  
% 2.42/1.34  Timing (in seconds)
% 2.42/1.34  ----------------------
% 2.42/1.34  Preprocessing        : 0.30
% 2.42/1.34  Parsing              : 0.17
% 2.42/1.34  CNF conversion       : 0.02
% 2.42/1.34  Main loop            : 0.25
% 2.42/1.34  Inferencing          : 0.10
% 2.42/1.34  Reduction            : 0.07
% 2.42/1.34  Demodulation         : 0.05
% 2.42/1.34  BG Simplification    : 0.01
% 2.42/1.34  Subsumption          : 0.06
% 2.42/1.34  Abstraction          : 0.01
% 2.42/1.34  MUC search           : 0.00
% 2.42/1.34  Cooper               : 0.00
% 2.42/1.34  Total                : 0.58
% 2.42/1.34  Index Insertion      : 0.00
% 2.42/1.34  Index Deletion       : 0.00
% 2.42/1.34  Index Matching       : 0.00
% 2.42/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
