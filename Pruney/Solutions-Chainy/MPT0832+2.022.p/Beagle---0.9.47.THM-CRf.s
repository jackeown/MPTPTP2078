%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:43 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 129 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 220 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( m1_subset_1(A_49,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51)))
      | ~ r1_tarski(A_49,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_207,plain,(
    ! [A_71,B_72,B_73,C_74] :
      ( m1_subset_1(k8_relat_1(A_71,B_72),k1_zfmisc_1(k2_zfmisc_1(B_73,C_74)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_zfmisc_1(B_73,C_74)))
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_16,plain,(
    ! [C_14,A_12,B_13] :
      ( v4_relat_1(C_14,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_587,plain,(
    ! [A_145,B_146,B_147,C_148] :
      ( v4_relat_1(k8_relat_1(A_145,B_146),B_147)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k2_zfmisc_1(B_147,C_148)))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_207,c_16])).

tff(c_597,plain,(
    ! [A_145] :
      ( v4_relat_1(k8_relat_1(A_145,'#skF_4'),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_587])).

tff(c_604,plain,(
    ! [A_145] : v4_relat_1(k8_relat_1(A_145,'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_597])).

tff(c_104,plain,(
    ! [A_59,B_60,B_61,C_62] :
      ( m1_subset_1(k8_relat_1(A_59,B_60),k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_59,B_60,B_61,C_62] :
      ( v1_relat_1(k8_relat_1(A_59,B_60))
      | ~ v1_relat_1(k2_zfmisc_1(B_61,C_62))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_171,plain,(
    ! [A_67,B_68,B_69,C_70] :
      ( v1_relat_1(k8_relat_1(A_67,B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_zfmisc_1(B_69,C_70)))
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118])).

tff(c_179,plain,(
    ! [A_67] :
      ( v1_relat_1(k8_relat_1(A_67,'#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_171])).

tff(c_185,plain,(
    ! [A_67] : v1_relat_1(k8_relat_1(A_67,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_179])).

tff(c_77,plain,(
    ! [C_53,A_54,B_55] :
      ( m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ r1_tarski(k2_relat_1(C_53),B_55)
      | ~ r1_tarski(k1_relat_1(C_53),A_54)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k6_relset_1(A_44,B_45,C_46,D_47) = k8_relat_1(C_46,D_47)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    ! [C_46] : k6_relset_1('#skF_3','#skF_1',C_46,'#skF_4') = k8_relat_1(C_46,'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_24,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_57,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_24])).

tff(c_92,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_77,c_57])).

tff(c_103,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_103])).

tff(c_190,plain,(
    v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_189,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_191,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_194,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_191])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_194])).

tff(c_199,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_203,plain,
    ( ~ v4_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_206,plain,(
    ~ v4_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_203])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.37  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.72/1.37  
% 2.72/1.37  %Foreground sorts:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Background operators:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Foreground operators:
% 2.72/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.37  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.72/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.72/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.72/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.37  
% 2.72/1.39  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.72/1.39  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.72/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.72/1.39  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.72/1.39  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 2.72/1.39  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.72/1.39  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.72/1.39  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.72/1.39  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.72/1.39  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.72/1.39  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.72/1.39  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.39  tff(c_30, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.39  tff(c_33, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_30])).
% 2.72/1.39  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_33])).
% 2.72/1.39  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.39  tff(c_67, plain, (![A_49, B_50, C_51, D_52]: (m1_subset_1(A_49, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))) | ~r1_tarski(A_49, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.72/1.39  tff(c_207, plain, (![A_71, B_72, B_73, C_74]: (m1_subset_1(k8_relat_1(A_71, B_72), k1_zfmisc_1(k2_zfmisc_1(B_73, C_74))) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_zfmisc_1(B_73, C_74))) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_12, c_67])).
% 2.72/1.39  tff(c_16, plain, (![C_14, A_12, B_13]: (v4_relat_1(C_14, A_12) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.39  tff(c_587, plain, (![A_145, B_146, B_147, C_148]: (v4_relat_1(k8_relat_1(A_145, B_146), B_147) | ~m1_subset_1(B_146, k1_zfmisc_1(k2_zfmisc_1(B_147, C_148))) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_207, c_16])).
% 2.72/1.39  tff(c_597, plain, (![A_145]: (v4_relat_1(k8_relat_1(A_145, '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_587])).
% 2.72/1.39  tff(c_604, plain, (![A_145]: (v4_relat_1(k8_relat_1(A_145, '#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_597])).
% 2.72/1.39  tff(c_104, plain, (![A_59, B_60, B_61, C_62]: (m1_subset_1(k8_relat_1(A_59, B_60), k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~m1_subset_1(B_60, k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_12, c_67])).
% 2.72/1.39  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.39  tff(c_118, plain, (![A_59, B_60, B_61, C_62]: (v1_relat_1(k8_relat_1(A_59, B_60)) | ~v1_relat_1(k2_zfmisc_1(B_61, C_62)) | ~m1_subset_1(B_60, k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_104, c_2])).
% 2.72/1.39  tff(c_171, plain, (![A_67, B_68, B_69, C_70]: (v1_relat_1(k8_relat_1(A_67, B_68)) | ~m1_subset_1(B_68, k1_zfmisc_1(k2_zfmisc_1(B_69, C_70))) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_118])).
% 2.72/1.39  tff(c_179, plain, (![A_67]: (v1_relat_1(k8_relat_1(A_67, '#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_171])).
% 2.72/1.39  tff(c_185, plain, (![A_67]: (v1_relat_1(k8_relat_1(A_67, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_179])).
% 2.72/1.39  tff(c_77, plain, (![C_53, A_54, B_55]: (m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~r1_tarski(k2_relat_1(C_53), B_55) | ~r1_tarski(k1_relat_1(C_53), A_54) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.39  tff(c_53, plain, (![A_44, B_45, C_46, D_47]: (k6_relset_1(A_44, B_45, C_46, D_47)=k8_relat_1(C_46, D_47) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.39  tff(c_56, plain, (![C_46]: (k6_relset_1('#skF_3', '#skF_1', C_46, '#skF_4')=k8_relat_1(C_46, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.72/1.39  tff(c_24, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.39  tff(c_57, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_24])).
% 2.72/1.39  tff(c_92, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_77, c_57])).
% 2.72/1.39  tff(c_103, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.72/1.39  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_103])).
% 2.72/1.39  tff(c_190, plain, (v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_92])).
% 2.72/1.39  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.39  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.39  tff(c_189, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_92])).
% 2.72/1.39  tff(c_191, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_189])).
% 2.72/1.39  tff(c_194, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_191])).
% 2.72/1.39  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_194])).
% 2.72/1.39  tff(c_199, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_189])).
% 2.72/1.39  tff(c_203, plain, (~v4_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_199])).
% 2.72/1.39  tff(c_206, plain, (~v4_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_203])).
% 2.72/1.39  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_604, c_206])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 0
% 2.72/1.39  #Sup     : 127
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 9
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 9
% 2.72/1.39  #Demod        : 40
% 2.72/1.39  #Tautology    : 8
% 2.72/1.39  #SimpNegUnit  : 0
% 2.72/1.39  #BackRed      : 3
% 2.72/1.39  
% 2.72/1.39  #Partial instantiations: 0
% 2.72/1.39  #Strategies tried      : 1
% 2.72/1.39  
% 2.72/1.39  Timing (in seconds)
% 2.72/1.39  ----------------------
% 2.72/1.39  Preprocessing        : 0.28
% 2.72/1.39  Parsing              : 0.15
% 2.72/1.39  CNF conversion       : 0.02
% 2.72/1.39  Main loop            : 0.32
% 2.72/1.39  Inferencing          : 0.13
% 2.72/1.39  Reduction            : 0.09
% 2.72/1.39  Demodulation         : 0.06
% 2.72/1.39  BG Simplification    : 0.02
% 2.72/1.39  Subsumption          : 0.06
% 2.72/1.39  Abstraction          : 0.02
% 2.72/1.39  MUC search           : 0.00
% 2.72/1.39  Cooper               : 0.00
% 2.72/1.39  Total                : 0.64
% 2.72/1.39  Index Insertion      : 0.00
% 2.72/1.39  Index Deletion       : 0.00
% 2.72/1.39  Index Matching       : 0.00
% 2.72/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
