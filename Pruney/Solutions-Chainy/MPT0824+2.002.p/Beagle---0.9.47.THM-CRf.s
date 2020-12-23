%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:13 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 136 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   78 ( 242 expanded)
%              Number of equality atoms :   29 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(k6_subset_1(A,B),C) = k6_subset_1(k8_relat_1(A,C),k8_relat_1(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

tff(c_14,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),A_11)
      | r1_tarski(k3_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [A_24] : k1_relat_1('#skF_3'(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    ! [A_24] : v1_relat_1('#skF_3'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74,plain,(
    ! [A_24] :
      ( k1_relat_1('#skF_3'(A_24)) != k1_xboole_0
      | '#skF_3'(A_24) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_84,plain,(
    ! [A_41] :
      ( k1_xboole_0 != A_41
      | '#skF_3'(A_41) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_74])).

tff(c_94,plain,(
    ! [A_41] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_41 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_40])).

tff(c_107,plain,(
    ! [A_41] : k1_xboole_0 != A_41 ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_14])).

tff(c_114,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_77,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k8_relat_1(A_39,B_40),B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [A_39] :
      ( k8_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_128,plain,(
    ! [A_39] : k8_relat_1(A_39,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_82])).

tff(c_20,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_20,C_22,B_21] :
      ( k6_subset_1(k8_relat_1(A_20,C_22),k8_relat_1(B_21,C_22)) = k8_relat_1(k6_subset_1(A_20,B_21),C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_227,plain,(
    ! [A_72,C_73,B_74] :
      ( k4_xboole_0(k8_relat_1(A_72,C_73),k8_relat_1(B_74,C_73)) = k8_relat_1(k4_xboole_0(A_72,B_74),C_73)
      | ~ v1_relat_1(C_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_28])).

tff(c_245,plain,(
    ! [A_39,B_74] :
      ( k8_relat_1(k4_xboole_0(A_39,B_74),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k8_relat_1(B_74,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_227])).

tff(c_252,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_128,c_128,c_245])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_264,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_44])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_271,plain,(
    ! [C_75] : ~ r2_hidden(C_75,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_264,c_2])).

tff(c_275,plain,(
    ! [B_12] : r1_tarski(k3_tarski(k1_xboole_0),B_12) ),
    inference(resolution,[status(thm)],[c_18,c_271])).

tff(c_285,plain,(
    ! [B_12] : r1_tarski(k1_xboole_0,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_275])).

tff(c_156,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_164,plain,(
    ~ r1_tarski(k1_xboole_0,k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_156,c_42])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.38  
% 2.24/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.48/1.39  
% 2.48/1.39  %Foreground sorts:
% 2.48/1.39  
% 2.48/1.39  
% 2.48/1.39  %Background operators:
% 2.48/1.39  
% 2.48/1.39  
% 2.48/1.39  %Foreground operators:
% 2.48/1.39  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.48/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.48/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.48/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.48/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.48/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.48/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.39  
% 2.48/1.40  tff(f_52, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.48/1.40  tff(f_59, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.48/1.40  tff(f_93, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.48/1.40  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.48/1.40  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 2.48/1.40  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.48/1.40  tff(f_61, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.48/1.40  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(k6_subset_1(A, B), C) = k6_subset_1(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_relat_1)).
% 2.48/1.40  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.48/1.40  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 2.48/1.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.48/1.40  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.40  tff(f_96, negated_conjecture, ~(![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relset_1)).
% 2.48/1.40  tff(c_14, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.48/1.40  tff(c_18, plain, (![A_11, B_12]: (r2_hidden('#skF_2'(A_11, B_12), A_11) | r1_tarski(k3_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.48/1.40  tff(c_36, plain, (![A_24]: (k1_relat_1('#skF_3'(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.48/1.40  tff(c_40, plain, (![A_24]: (v1_relat_1('#skF_3'(A_24)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.48/1.40  tff(c_71, plain, (![A_38]: (k1_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.48/1.40  tff(c_74, plain, (![A_24]: (k1_relat_1('#skF_3'(A_24))!=k1_xboole_0 | '#skF_3'(A_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_71])).
% 2.48/1.40  tff(c_84, plain, (![A_41]: (k1_xboole_0!=A_41 | '#skF_3'(A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_74])).
% 2.48/1.40  tff(c_94, plain, (![A_41]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_41)), inference(superposition, [status(thm), theory('equality')], [c_84, c_40])).
% 2.48/1.40  tff(c_107, plain, (![A_41]: (k1_xboole_0!=A_41)), inference(splitLeft, [status(thm)], [c_94])).
% 2.48/1.40  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_14])).
% 2.48/1.40  tff(c_114, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_94])).
% 2.48/1.40  tff(c_77, plain, (![A_39, B_40]: (r1_tarski(k8_relat_1(A_39, B_40), B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.48/1.40  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.48/1.40  tff(c_82, plain, (![A_39]: (k8_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_77, c_8])).
% 2.48/1.40  tff(c_128, plain, (![A_39]: (k8_relat_1(A_39, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_82])).
% 2.48/1.40  tff(c_20, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.40  tff(c_28, plain, (![A_20, C_22, B_21]: (k6_subset_1(k8_relat_1(A_20, C_22), k8_relat_1(B_21, C_22))=k8_relat_1(k6_subset_1(A_20, B_21), C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.48/1.40  tff(c_227, plain, (![A_72, C_73, B_74]: (k4_xboole_0(k8_relat_1(A_72, C_73), k8_relat_1(B_74, C_73))=k8_relat_1(k4_xboole_0(A_72, B_74), C_73) | ~v1_relat_1(C_73))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_28])).
% 2.48/1.40  tff(c_245, plain, (![A_39, B_74]: (k8_relat_1(k4_xboole_0(A_39, B_74), k1_xboole_0)=k4_xboole_0(k1_xboole_0, k8_relat_1(B_74, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_227])).
% 2.48/1.40  tff(c_252, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_128, c_128, c_245])).
% 2.48/1.40  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.48/1.40  tff(c_12, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, k3_xboole_0(A_9, B_10)), B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.48/1.40  tff(c_44, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.48/1.40  tff(c_264, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_252, c_44])).
% 2.48/1.40  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.40  tff(c_271, plain, (![C_75]: (~r2_hidden(C_75, k1_xboole_0))), inference(resolution, [status(thm)], [c_264, c_2])).
% 2.48/1.40  tff(c_275, plain, (![B_12]: (r1_tarski(k3_tarski(k1_xboole_0), B_12))), inference(resolution, [status(thm)], [c_18, c_271])).
% 2.48/1.40  tff(c_285, plain, (![B_12]: (r1_tarski(k1_xboole_0, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_275])).
% 2.48/1.40  tff(c_156, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.40  tff(c_42, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.48/1.40  tff(c_164, plain, (~r1_tarski(k1_xboole_0, k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_156, c_42])).
% 2.48/1.40  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_164])).
% 2.48/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.40  
% 2.48/1.40  Inference rules
% 2.48/1.40  ----------------------
% 2.48/1.40  #Ref     : 1
% 2.48/1.40  #Sup     : 54
% 2.48/1.40  #Fact    : 0
% 2.48/1.40  #Define  : 0
% 2.48/1.40  #Split   : 2
% 2.48/1.40  #Chain   : 0
% 2.48/1.40  #Close   : 0
% 2.48/1.40  
% 2.48/1.40  Ordering : KBO
% 2.48/1.40  
% 2.48/1.40  Simplification rules
% 2.48/1.40  ----------------------
% 2.48/1.40  #Subsume      : 7
% 2.48/1.40  #Demod        : 17
% 2.48/1.40  #Tautology    : 25
% 2.48/1.40  #SimpNegUnit  : 8
% 2.48/1.40  #BackRed      : 5
% 2.48/1.40  
% 2.48/1.40  #Partial instantiations: 0
% 2.48/1.40  #Strategies tried      : 1
% 2.48/1.40  
% 2.48/1.40  Timing (in seconds)
% 2.48/1.40  ----------------------
% 2.48/1.40  Preprocessing        : 0.34
% 2.48/1.40  Parsing              : 0.18
% 2.48/1.41  CNF conversion       : 0.02
% 2.48/1.41  Main loop            : 0.22
% 2.48/1.41  Inferencing          : 0.08
% 2.48/1.41  Reduction            : 0.07
% 2.48/1.41  Demodulation         : 0.05
% 2.48/1.41  BG Simplification    : 0.01
% 2.48/1.41  Subsumption          : 0.03
% 2.48/1.41  Abstraction          : 0.01
% 2.48/1.41  MUC search           : 0.00
% 2.48/1.41  Cooper               : 0.00
% 2.48/1.41  Total                : 0.60
% 2.48/1.41  Index Insertion      : 0.00
% 2.48/1.41  Index Deletion       : 0.00
% 2.48/1.41  Index Matching       : 0.00
% 2.48/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
