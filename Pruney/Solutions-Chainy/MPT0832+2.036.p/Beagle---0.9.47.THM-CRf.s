%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:45 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 113 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 194 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_16,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_43,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_49,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_53,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_49])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_16,B_17)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k8_relat_1(A_18,B_19),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_33,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_41,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_zfmisc_1(A_1),k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_49,C_50,B_51] :
      ( m1_subset_1(A_49,C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [A_53,B_54,A_55] :
      ( m1_subset_1(A_53,B_54)
      | ~ r2_hidden(A_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_146,plain,(
    ! [A_71,B_72,B_73] :
      ( m1_subset_1(A_71,B_72)
      | ~ r1_tarski(B_73,B_72)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(A_71,B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_150,plain,(
    ! [A_71,B_2,A_1] :
      ( m1_subset_1(A_71,k1_zfmisc_1(B_2))
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_71,k1_zfmisc_1(A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_162,plain,(
    ! [A_74,B_75,A_76] :
      ( m1_subset_1(A_74,k1_zfmisc_1(B_75))
      | ~ m1_subset_1(A_74,k1_zfmisc_1(A_76))
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_150])).

tff(c_173,plain,(
    ! [A_78,B_79,B_80] :
      ( m1_subset_1(A_78,k1_zfmisc_1(B_79))
      | ~ r1_tarski(B_80,B_79)
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_186,plain,(
    ! [A_81] :
      ( m1_subset_1(A_81,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ r1_tarski(A_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41,c_173])).

tff(c_24,plain,(
    ! [D_27,C_26,B_25,A_24] :
      ( m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(C_26,B_25)))
      | ~ r1_tarski(k2_relat_1(D_27),B_25)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(C_26,A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_415,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1(A_124,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_125)))
      | ~ r1_tarski(k2_relat_1(A_124),B_125)
      | ~ r1_tarski(A_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_186,c_24])).

tff(c_92,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k6_relset_1(A_56,B_57,C_58,D_59) = k8_relat_1(C_58,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_99,plain,(
    ! [C_58] : k6_relset_1('#skF_3','#skF_1',C_58,'#skF_4') = k8_relat_1(C_58,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_26,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_101,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_26])).

tff(c_435,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_415,c_101])).

tff(c_442,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_445,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_442])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_445])).

tff(c_450,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_477,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_450])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.80/1.44  
% 2.80/1.44  %Foreground sorts:
% 2.80/1.44  
% 2.80/1.44  
% 2.80/1.44  %Background operators:
% 2.80/1.44  
% 2.80/1.44  
% 2.80/1.44  %Foreground operators:
% 2.80/1.44  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.44  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.80/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.44  
% 2.80/1.46  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.80/1.46  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.80/1.46  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.80/1.46  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.80/1.46  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.80/1.46  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.80/1.46  tff(f_32, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.80/1.46  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.80/1.46  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.80/1.46  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.80/1.46  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 2.80/1.46  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.80/1.46  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.46  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.80/1.46  tff(c_43, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.46  tff(c_49, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.80/1.46  tff(c_53, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_49])).
% 2.80/1.46  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k2_relat_1(k8_relat_1(A_16, B_17)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.80/1.46  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k8_relat_1(A_18, B_19), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.46  tff(c_33, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.46  tff(c_41, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_33])).
% 2.80/1.46  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.46  tff(c_4, plain, (![A_3]: (~v1_xboole_0(k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.46  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k1_zfmisc_1(A_1), k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.46  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.46  tff(c_80, plain, (![A_49, C_50, B_51]: (m1_subset_1(A_49, C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.46  tff(c_88, plain, (![A_53, B_54, A_55]: (m1_subset_1(A_53, B_54) | ~r2_hidden(A_53, A_55) | ~r1_tarski(A_55, B_54))), inference(resolution, [status(thm)], [c_10, c_80])).
% 2.80/1.46  tff(c_146, plain, (![A_71, B_72, B_73]: (m1_subset_1(A_71, B_72) | ~r1_tarski(B_73, B_72) | v1_xboole_0(B_73) | ~m1_subset_1(A_71, B_73))), inference(resolution, [status(thm)], [c_6, c_88])).
% 2.80/1.46  tff(c_150, plain, (![A_71, B_2, A_1]: (m1_subset_1(A_71, k1_zfmisc_1(B_2)) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_71, k1_zfmisc_1(A_1)) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_146])).
% 2.80/1.46  tff(c_162, plain, (![A_74, B_75, A_76]: (m1_subset_1(A_74, k1_zfmisc_1(B_75)) | ~m1_subset_1(A_74, k1_zfmisc_1(A_76)) | ~r1_tarski(A_76, B_75))), inference(negUnitSimplification, [status(thm)], [c_4, c_150])).
% 2.80/1.46  tff(c_173, plain, (![A_78, B_79, B_80]: (m1_subset_1(A_78, k1_zfmisc_1(B_79)) | ~r1_tarski(B_80, B_79) | ~r1_tarski(A_78, B_80))), inference(resolution, [status(thm)], [c_10, c_162])).
% 2.80/1.46  tff(c_186, plain, (![A_81]: (m1_subset_1(A_81, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~r1_tarski(A_81, '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_173])).
% 2.80/1.46  tff(c_24, plain, (![D_27, C_26, B_25, A_24]: (m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(C_26, B_25))) | ~r1_tarski(k2_relat_1(D_27), B_25) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(C_26, A_24))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.46  tff(c_415, plain, (![A_124, B_125]: (m1_subset_1(A_124, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_125))) | ~r1_tarski(k2_relat_1(A_124), B_125) | ~r1_tarski(A_124, '#skF_4'))), inference(resolution, [status(thm)], [c_186, c_24])).
% 2.80/1.46  tff(c_92, plain, (![A_56, B_57, C_58, D_59]: (k6_relset_1(A_56, B_57, C_58, D_59)=k8_relat_1(C_58, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.80/1.46  tff(c_99, plain, (![C_58]: (k6_relset_1('#skF_3', '#skF_1', C_58, '#skF_4')=k8_relat_1(C_58, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_92])).
% 2.80/1.46  tff(c_26, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.80/1.46  tff(c_101, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_26])).
% 2.80/1.46  tff(c_435, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_415, c_101])).
% 2.80/1.46  tff(c_442, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_435])).
% 2.80/1.46  tff(c_445, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_442])).
% 2.80/1.46  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_445])).
% 2.80/1.46  tff(c_450, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_435])).
% 2.80/1.46  tff(c_477, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_450])).
% 2.80/1.46  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_477])).
% 2.80/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.46  
% 2.80/1.46  Inference rules
% 2.80/1.46  ----------------------
% 2.80/1.46  #Ref     : 0
% 2.80/1.46  #Sup     : 101
% 2.80/1.46  #Fact    : 0
% 2.80/1.46  #Define  : 0
% 2.80/1.46  #Split   : 4
% 2.80/1.46  #Chain   : 0
% 2.80/1.46  #Close   : 0
% 2.80/1.46  
% 2.80/1.46  Ordering : KBO
% 2.80/1.46  
% 2.80/1.46  Simplification rules
% 2.80/1.46  ----------------------
% 2.80/1.46  #Subsume      : 9
% 2.80/1.46  #Demod        : 22
% 2.80/1.46  #Tautology    : 12
% 2.80/1.46  #SimpNegUnit  : 2
% 2.80/1.46  #BackRed      : 2
% 2.80/1.46  
% 2.80/1.46  #Partial instantiations: 0
% 2.80/1.46  #Strategies tried      : 1
% 2.80/1.46  
% 2.80/1.46  Timing (in seconds)
% 2.80/1.46  ----------------------
% 2.80/1.46  Preprocessing        : 0.31
% 2.80/1.46  Parsing              : 0.18
% 2.80/1.46  CNF conversion       : 0.02
% 2.80/1.46  Main loop            : 0.31
% 2.80/1.46  Inferencing          : 0.12
% 2.80/1.46  Reduction            : 0.08
% 2.80/1.46  Demodulation         : 0.05
% 2.80/1.46  BG Simplification    : 0.02
% 2.80/1.46  Subsumption          : 0.07
% 2.80/1.46  Abstraction          : 0.02
% 2.80/1.46  MUC search           : 0.00
% 2.80/1.46  Cooper               : 0.00
% 2.80/1.46  Total                : 0.65
% 2.80/1.46  Index Insertion      : 0.00
% 2.80/1.46  Index Deletion       : 0.00
% 2.80/1.46  Index Matching       : 0.00
% 2.80/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
