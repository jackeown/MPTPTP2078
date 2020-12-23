%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:42 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 129 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 200 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_wellord1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_14,B_15)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k8_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_16,B_17)),k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_81])).

tff(c_165,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k1_relset_1(A_75,B_76,C_77),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_179,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_165])).

tff(c_184,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_179])).

tff(c_16,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | v1_xboole_0(B_47)
      | ~ m1_subset_1(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_46,A_4] :
      ( r1_tarski(A_46,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_46,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_60,plain,(
    ! [A_46,A_4] :
      ( r1_tarski(A_46,A_4)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(A_4)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_57])).

tff(c_194,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_60])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    ! [A_80] :
      ( r1_tarski(A_80,'#skF_5')
      | ~ r1_tarski(A_80,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_194,c_2])).

tff(c_209,plain,(
    ! [A_16] :
      ( r1_tarski(k1_relat_1(k8_relat_1(A_16,'#skF_6')),'#skF_5')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_201])).

tff(c_217,plain,(
    ! [A_16] : r1_tarski(k1_relat_1(k8_relat_1(A_16,'#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_209])).

tff(c_348,plain,(
    ! [C_105,A_106,B_107] :
      ( m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ r1_tarski(k2_relat_1(C_105),B_107)
      | ~ r1_tarski(k1_relat_1(C_105),A_106)
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_257,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k6_relset_1(A_86,B_87,C_88,D_89) = k8_relat_1(C_88,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_264,plain,(
    ! [C_88] : k6_relset_1('#skF_5','#skF_3',C_88,'#skF_6') = k8_relat_1(C_88,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_257])).

tff(c_36,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_5','#skF_3','#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_265,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_4','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_36])).

tff(c_353,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_5')
    | ~ v1_relat_1(k8_relat_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_348,c_265])).

tff(c_368,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_353])).

tff(c_373,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_376,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_373])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_376])).

tff(c_381,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_4','#skF_6')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_385,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_381])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.36/1.35  
% 2.36/1.35  %Foreground sorts:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Background operators:
% 2.36/1.35  
% 2.36/1.35  
% 2.36/1.35  %Foreground operators:
% 2.36/1.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.35  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.36/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.35  
% 2.53/1.37  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.53/1.37  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.53/1.37  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.53/1.37  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.53/1.37  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_wellord1)).
% 2.53/1.37  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.53/1.37  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.53/1.37  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.53/1.37  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.53/1.37  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.53/1.37  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.53/1.37  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.53/1.37  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.53/1.37  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.53/1.37  tff(c_48, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.53/1.37  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_48])).
% 2.53/1.37  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(k2_relat_1(k8_relat_1(A_14, B_15)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.37  tff(c_20, plain, (![A_12, B_13]: (v1_relat_1(k8_relat_1(A_12, B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.37  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(k1_relat_1(k8_relat_1(A_16, B_17)), k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.37  tff(c_81, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.37  tff(c_85, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_81])).
% 2.53/1.37  tff(c_165, plain, (![A_75, B_76, C_77]: (m1_subset_1(k1_relset_1(A_75, B_76, C_77), k1_zfmisc_1(A_75)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.37  tff(c_179, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_85, c_165])).
% 2.53/1.37  tff(c_184, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_179])).
% 2.53/1.37  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.37  tff(c_53, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | v1_xboole_0(B_47) | ~m1_subset_1(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.37  tff(c_4, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.37  tff(c_57, plain, (![A_46, A_4]: (r1_tarski(A_46, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_46, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_53, c_4])).
% 2.53/1.37  tff(c_60, plain, (![A_46, A_4]: (r1_tarski(A_46, A_4) | ~m1_subset_1(A_46, k1_zfmisc_1(A_4)))), inference(negUnitSimplification, [status(thm)], [c_16, c_57])).
% 2.53/1.37  tff(c_194, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_184, c_60])).
% 2.53/1.37  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.37  tff(c_201, plain, (![A_80]: (r1_tarski(A_80, '#skF_5') | ~r1_tarski(A_80, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_194, c_2])).
% 2.53/1.37  tff(c_209, plain, (![A_16]: (r1_tarski(k1_relat_1(k8_relat_1(A_16, '#skF_6')), '#skF_5') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_201])).
% 2.53/1.37  tff(c_217, plain, (![A_16]: (r1_tarski(k1_relat_1(k8_relat_1(A_16, '#skF_6')), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_209])).
% 2.53/1.37  tff(c_348, plain, (![C_105, A_106, B_107]: (m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~r1_tarski(k2_relat_1(C_105), B_107) | ~r1_tarski(k1_relat_1(C_105), A_106) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.53/1.37  tff(c_257, plain, (![A_86, B_87, C_88, D_89]: (k6_relset_1(A_86, B_87, C_88, D_89)=k8_relat_1(C_88, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.37  tff(c_264, plain, (![C_88]: (k6_relset_1('#skF_5', '#skF_3', C_88, '#skF_6')=k8_relat_1(C_88, '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_257])).
% 2.53/1.37  tff(c_36, plain, (~m1_subset_1(k6_relset_1('#skF_5', '#skF_3', '#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.53/1.37  tff(c_265, plain, (~m1_subset_1(k8_relat_1('#skF_4', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_36])).
% 2.53/1.37  tff(c_353, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_4') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_348, c_265])).
% 2.53/1.37  tff(c_368, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_4') | ~v1_relat_1(k8_relat_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_353])).
% 2.53/1.37  tff(c_373, plain, (~v1_relat_1(k8_relat_1('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_368])).
% 2.53/1.37  tff(c_376, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_373])).
% 2.53/1.37  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_376])).
% 2.53/1.37  tff(c_381, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_4', '#skF_6')), '#skF_4')), inference(splitRight, [status(thm)], [c_368])).
% 2.53/1.37  tff(c_385, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_381])).
% 2.53/1.37  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_385])).
% 2.53/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  Inference rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Ref     : 0
% 2.53/1.37  #Sup     : 77
% 2.53/1.37  #Fact    : 0
% 2.53/1.37  #Define  : 0
% 2.53/1.37  #Split   : 2
% 2.53/1.37  #Chain   : 0
% 2.53/1.37  #Close   : 0
% 2.53/1.37  
% 2.53/1.37  Ordering : KBO
% 2.53/1.37  
% 2.53/1.37  Simplification rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Subsume      : 8
% 2.53/1.37  #Demod        : 9
% 2.53/1.37  #Tautology    : 8
% 2.53/1.37  #SimpNegUnit  : 1
% 2.53/1.37  #BackRed      : 1
% 2.53/1.37  
% 2.53/1.37  #Partial instantiations: 0
% 2.53/1.37  #Strategies tried      : 1
% 2.53/1.37  
% 2.53/1.37  Timing (in seconds)
% 2.53/1.37  ----------------------
% 2.53/1.37  Preprocessing        : 0.32
% 2.53/1.37  Parsing              : 0.17
% 2.53/1.37  CNF conversion       : 0.02
% 2.53/1.37  Main loop            : 0.26
% 2.53/1.37  Inferencing          : 0.10
% 2.53/1.37  Reduction            : 0.07
% 2.53/1.37  Demodulation         : 0.04
% 2.53/1.37  BG Simplification    : 0.02
% 2.53/1.37  Subsumption          : 0.06
% 2.53/1.37  Abstraction          : 0.01
% 2.53/1.37  MUC search           : 0.00
% 2.53/1.37  Cooper               : 0.00
% 2.53/1.37  Total                : 0.61
% 2.53/1.37  Index Insertion      : 0.00
% 2.53/1.37  Index Deletion       : 0.00
% 2.53/1.37  Index Matching       : 0.00
% 2.53/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
