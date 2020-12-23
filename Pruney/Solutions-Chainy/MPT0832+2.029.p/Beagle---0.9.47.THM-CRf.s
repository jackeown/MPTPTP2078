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
% DateTime   : Thu Dec  3 10:07:44 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 116 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 183 expanded)
%              Number of equality atoms :    7 (   7 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

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

tff(c_36,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_36])).

tff(c_174,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(A_69,C_70)
      | ~ r1_tarski(B_71,C_70)
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_174])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_218,plain,(
    ! [A_73] :
      ( v1_relat_1(A_73)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1'))
      | ~ r1_tarski(A_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_207,c_53])).

tff(c_225,plain,(
    ! [A_74] :
      ( v1_relat_1(A_74)
      | ~ r1_tarski(A_74,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_218])).

tff(c_237,plain,(
    ! [A_13] :
      ( v1_relat_1(k8_relat_1(A_13,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_225])).

tff(c_242,plain,(
    ! [A_13] : v1_relat_1(k8_relat_1(A_13,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_237])).

tff(c_251,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_79,B_80)),k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_82,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_91,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_150,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(B_67,A_68) = B_67
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_150])).

tff(c_160,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_156])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_18,A_17)),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_164,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_18])).

tff(c_168,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_164])).

tff(c_185,plain,(
    ! [A_69] :
      ( r1_tarski(A_69,'#skF_3')
      | ~ r1_tarski(A_69,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_168,c_174])).

tff(c_255,plain,(
    ! [A_79] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_79,'#skF_4')),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_251,c_185])).

tff(c_263,plain,(
    ! [A_79] : r1_tarski(k1_relat_1(k8_relat_1(A_79,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_255])).

tff(c_415,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ r1_tarski(k2_relat_1(C_100),B_102)
      | ~ r1_tarski(k1_relat_1(C_100),A_101)
      | ~ v1_relat_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_346,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k6_relset_1(A_91,B_92,C_93,D_94) = k8_relat_1(C_93,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_353,plain,(
    ! [C_93] : k6_relset_1('#skF_3','#skF_1',C_93,'#skF_4') = k8_relat_1(C_93,'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_346])).

tff(c_30,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_355,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_30])).

tff(c_418,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_415,c_355])).

tff(c_435,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_263,c_418])).

tff(c_445,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_435])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.31  
% 2.25/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.31  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.25/1.31  
% 2.25/1.31  %Foreground sorts:
% 2.25/1.31  
% 2.25/1.31  
% 2.25/1.31  %Background operators:
% 2.25/1.31  
% 2.25/1.31  
% 2.25/1.31  %Foreground operators:
% 2.25/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.31  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.25/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.25/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.25/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.32  
% 2.25/1.33  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.25/1.33  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.25/1.33  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.25/1.33  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.25/1.33  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.25/1.33  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.33  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.25/1.33  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_wellord1)).
% 2.25/1.33  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.25/1.33  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.25/1.33  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.25/1.33  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.25/1.33  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.25/1.33  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.33  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.33  tff(c_46, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.33  tff(c_52, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_46])).
% 2.25/1.33  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 2.25/1.33  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k2_relat_1(k8_relat_1(A_11, B_12)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.33  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k8_relat_1(A_13, B_14), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.33  tff(c_36, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.33  tff(c_44, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_36])).
% 2.25/1.33  tff(c_174, plain, (![A_69, C_70, B_71]: (r1_tarski(A_69, C_70) | ~r1_tarski(B_71, C_70) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.33  tff(c_207, plain, (![A_73]: (r1_tarski(A_73, k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_73, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_174])).
% 2.25/1.33  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.33  tff(c_53, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_46])).
% 2.25/1.33  tff(c_218, plain, (![A_73]: (v1_relat_1(A_73) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1')) | ~r1_tarski(A_73, '#skF_4'))), inference(resolution, [status(thm)], [c_207, c_53])).
% 2.25/1.33  tff(c_225, plain, (![A_74]: (v1_relat_1(A_74) | ~r1_tarski(A_74, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_218])).
% 2.25/1.33  tff(c_237, plain, (![A_13]: (v1_relat_1(k8_relat_1(A_13, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_225])).
% 2.25/1.33  tff(c_242, plain, (![A_13]: (v1_relat_1(k8_relat_1(A_13, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_237])).
% 2.25/1.33  tff(c_251, plain, (![A_79, B_80]: (r1_tarski(k1_relat_1(k8_relat_1(A_79, B_80)), k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.33  tff(c_82, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.25/1.33  tff(c_91, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_82])).
% 2.25/1.33  tff(c_150, plain, (![B_67, A_68]: (k7_relat_1(B_67, A_68)=B_67 | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.33  tff(c_156, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_150])).
% 2.25/1.33  tff(c_160, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_156])).
% 2.25/1.33  tff(c_18, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(k7_relat_1(B_18, A_17)), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.33  tff(c_164, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_160, c_18])).
% 2.25/1.33  tff(c_168, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_164])).
% 2.25/1.33  tff(c_185, plain, (![A_69]: (r1_tarski(A_69, '#skF_3') | ~r1_tarski(A_69, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_168, c_174])).
% 2.25/1.33  tff(c_255, plain, (![A_79]: (r1_tarski(k1_relat_1(k8_relat_1(A_79, '#skF_4')), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_251, c_185])).
% 2.25/1.33  tff(c_263, plain, (![A_79]: (r1_tarski(k1_relat_1(k8_relat_1(A_79, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_255])).
% 2.25/1.33  tff(c_415, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~r1_tarski(k2_relat_1(C_100), B_102) | ~r1_tarski(k1_relat_1(C_100), A_101) | ~v1_relat_1(C_100))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.25/1.33  tff(c_346, plain, (![A_91, B_92, C_93, D_94]: (k6_relset_1(A_91, B_92, C_93, D_94)=k8_relat_1(C_93, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.25/1.33  tff(c_353, plain, (![C_93]: (k6_relset_1('#skF_3', '#skF_1', C_93, '#skF_4')=k8_relat_1(C_93, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_346])).
% 2.25/1.33  tff(c_30, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.25/1.33  tff(c_355, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_30])).
% 2.25/1.33  tff(c_418, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_415, c_355])).
% 2.25/1.33  tff(c_435, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_263, c_418])).
% 2.25/1.33  tff(c_445, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_435])).
% 2.25/1.33  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_445])).
% 2.25/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.33  
% 2.25/1.33  Inference rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Ref     : 0
% 2.25/1.33  #Sup     : 86
% 2.25/1.33  #Fact    : 0
% 2.25/1.33  #Define  : 0
% 2.25/1.33  #Split   : 3
% 2.25/1.33  #Chain   : 0
% 2.25/1.33  #Close   : 0
% 2.25/1.33  
% 2.25/1.33  Ordering : KBO
% 2.25/1.33  
% 2.25/1.33  Simplification rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Subsume      : 10
% 2.25/1.33  #Demod        : 26
% 2.25/1.33  #Tautology    : 13
% 2.25/1.33  #SimpNegUnit  : 0
% 2.25/1.33  #BackRed      : 2
% 2.25/1.33  
% 2.25/1.33  #Partial instantiations: 0
% 2.25/1.33  #Strategies tried      : 1
% 2.25/1.33  
% 2.25/1.33  Timing (in seconds)
% 2.25/1.33  ----------------------
% 2.25/1.33  Preprocessing        : 0.31
% 2.25/1.33  Parsing              : 0.17
% 2.25/1.33  CNF conversion       : 0.02
% 2.25/1.33  Main loop            : 0.26
% 2.25/1.33  Inferencing          : 0.10
% 2.25/1.34  Reduction            : 0.08
% 2.25/1.34  Demodulation         : 0.05
% 2.25/1.34  BG Simplification    : 0.01
% 2.25/1.34  Subsumption          : 0.05
% 2.25/1.34  Abstraction          : 0.01
% 2.25/1.34  MUC search           : 0.00
% 2.25/1.34  Cooper               : 0.00
% 2.25/1.34  Total                : 0.60
% 2.25/1.34  Index Insertion      : 0.00
% 2.25/1.34  Index Deletion       : 0.00
% 2.25/1.34  Index Matching       : 0.00
% 2.25/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
