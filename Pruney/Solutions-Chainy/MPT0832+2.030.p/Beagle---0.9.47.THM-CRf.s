%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:44 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 141 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 224 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_63,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_19,B_20)),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k8_relat_1(A_15,B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_21,B_22)),k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_86,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_160,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k1_relset_1(A_76,B_77,C_78),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_173,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_160])).

tff(c_178,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_173])).

tff(c_16,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    ! [A_45,A_4] :
      ( r1_tarski(A_45,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_57,plain,(
    ! [A_45,A_4] :
      ( r1_tarski(A_45,A_4)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_4)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_54])).

tff(c_195,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_178,c_57])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_5')
      | ~ r1_tarski(A_82,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_218,plain,(
    ! [A_21] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_21,'#skF_6')),'#skF_5')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_210])).

tff(c_226,plain,(
    ! [A_21] : r1_tarski(k1_relat_1(k8_relat_1(A_21,'#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_218])).

tff(c_311,plain,(
    ! [C_101,A_102,B_103] :
      ( m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ r1_tarski(k2_relat_1(C_101),B_103)
      | ~ r1_tarski(k1_relat_1(C_101),A_102)
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_236,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k6_relset_1(A_84,B_85,C_86,D_87) = k8_relat_1(C_86,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_243,plain,(
    ! [C_86] : k6_relset_1('#skF_5','#skF_3',C_86,'#skF_6') = k8_relat_1(C_86,'#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_236])).

tff(c_38,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_5','#skF_3','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_244,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_38])).

tff(c_316,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_5')
    | ~ v1_relat_1(k8_relat_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_311,c_244])).

tff(c_331,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_316])).

tff(c_338,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_341,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_338])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_341])).

tff(c_346,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_350,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_346])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.50  
% 2.04/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.04/1.50  
% 2.04/1.50  %Foreground sorts:
% 2.04/1.50  
% 2.04/1.50  
% 2.04/1.50  %Background operators:
% 2.04/1.50  
% 2.04/1.50  
% 2.04/1.50  %Foreground operators:
% 2.04/1.50  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.04/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.50  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.04/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.50  tff('#skF_6', type, '#skF_6': $i).
% 2.04/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.04/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.50  
% 2.41/1.51  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.41/1.51  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.41/1.51  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.41/1.51  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.41/1.51  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.41/1.51  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_wellord1)).
% 2.41/1.51  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.41/1.51  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.41/1.51  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.41/1.51  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.41/1.51  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.41/1.51  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.41/1.51  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.41/1.51  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.41/1.51  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.51  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.41/1.51  tff(c_63, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.51  tff(c_66, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_63])).
% 2.41/1.51  tff(c_69, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 2.41/1.51  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k2_relat_1(k8_relat_1(A_19, B_20)), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.41/1.51  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k8_relat_1(A_15, B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.51  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(k1_relat_1(k8_relat_1(A_21, B_22)), k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.41/1.51  tff(c_82, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.51  tff(c_86, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_82])).
% 2.41/1.51  tff(c_160, plain, (![A_76, B_77, C_78]: (m1_subset_1(k1_relset_1(A_76, B_77, C_78), k1_zfmisc_1(A_76)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.41/1.51  tff(c_173, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_160])).
% 2.41/1.51  tff(c_178, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_173])).
% 2.41/1.51  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.51  tff(c_50, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.41/1.51  tff(c_4, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.41/1.51  tff(c_54, plain, (![A_45, A_4]: (r1_tarski(A_45, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_45, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_50, c_4])).
% 2.41/1.51  tff(c_57, plain, (![A_45, A_4]: (r1_tarski(A_45, A_4) | ~m1_subset_1(A_45, k1_zfmisc_1(A_4)))), inference(negUnitSimplification, [status(thm)], [c_16, c_54])).
% 2.41/1.51  tff(c_195, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_178, c_57])).
% 2.41/1.51  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.51  tff(c_210, plain, (![A_82]: (r1_tarski(A_82, '#skF_5') | ~r1_tarski(A_82, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_195, c_2])).
% 2.41/1.51  tff(c_218, plain, (![A_21]: (r1_tarski(k1_relat_1(k8_relat_1(A_21, '#skF_6')), '#skF_5') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_28, c_210])).
% 2.41/1.51  tff(c_226, plain, (![A_21]: (r1_tarski(k1_relat_1(k8_relat_1(A_21, '#skF_6')), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_218])).
% 2.41/1.51  tff(c_311, plain, (![C_101, A_102, B_103]: (m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~r1_tarski(k2_relat_1(C_101), B_103) | ~r1_tarski(k1_relat_1(C_101), A_102) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.41/1.51  tff(c_236, plain, (![A_84, B_85, C_86, D_87]: (k6_relset_1(A_84, B_85, C_86, D_87)=k8_relat_1(C_86, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.41/1.51  tff(c_243, plain, (![C_86]: (k6_relset_1('#skF_5', '#skF_3', C_86, '#skF_6')=k8_relat_1(C_86, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_236])).
% 2.41/1.51  tff(c_38, plain, (~m1_subset_1(k6_relset_1('#skF_5', '#skF_3', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.41/1.51  tff(c_244, plain, (~m1_subset_1(k8_relat_1('#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_38])).
% 2.41/1.51  tff(c_316, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_4') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_311, c_244])).
% 2.41/1.51  tff(c_331, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_4') | ~v1_relat_1(k8_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_316])).
% 2.41/1.51  tff(c_338, plain, (~v1_relat_1(k8_relat_1('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_331])).
% 2.41/1.51  tff(c_341, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_338])).
% 2.41/1.51  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_341])).
% 2.41/1.51  tff(c_346, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_4')), inference(splitRight, [status(thm)], [c_331])).
% 2.41/1.51  tff(c_350, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_346])).
% 2.41/1.51  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_350])).
% 2.41/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.51  
% 2.41/1.51  Inference rules
% 2.41/1.51  ----------------------
% 2.41/1.51  #Ref     : 0
% 2.41/1.51  #Sup     : 67
% 2.41/1.51  #Fact    : 0
% 2.41/1.51  #Define  : 0
% 2.41/1.51  #Split   : 3
% 2.41/1.51  #Chain   : 0
% 2.41/1.51  #Close   : 0
% 2.41/1.51  
% 2.41/1.51  Ordering : KBO
% 2.41/1.51  
% 2.41/1.51  Simplification rules
% 2.41/1.51  ----------------------
% 2.41/1.52  #Subsume      : 6
% 2.41/1.52  #Demod        : 11
% 2.41/1.52  #Tautology    : 8
% 2.41/1.52  #SimpNegUnit  : 1
% 2.41/1.52  #BackRed      : 1
% 2.41/1.52  
% 2.41/1.52  #Partial instantiations: 0
% 2.41/1.52  #Strategies tried      : 1
% 2.41/1.52  
% 2.41/1.52  Timing (in seconds)
% 2.41/1.52  ----------------------
% 2.41/1.52  Preprocessing        : 0.28
% 2.41/1.52  Parsing              : 0.15
% 2.41/1.52  CNF conversion       : 0.02
% 2.41/1.52  Main loop            : 0.25
% 2.41/1.52  Inferencing          : 0.09
% 2.41/1.52  Reduction            : 0.07
% 2.41/1.52  Demodulation         : 0.04
% 2.41/1.52  BG Simplification    : 0.02
% 2.41/1.52  Subsumption          : 0.05
% 2.41/1.52  Abstraction          : 0.02
% 2.41/1.52  MUC search           : 0.00
% 2.41/1.52  Cooper               : 0.00
% 2.41/1.52  Total                : 0.56
% 2.41/1.52  Index Insertion      : 0.00
% 2.41/1.52  Index Deletion       : 0.00
% 2.41/1.52  Index Matching       : 0.00
% 2.41/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
