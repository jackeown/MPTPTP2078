%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:48 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   72 (  91 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 137 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_34])).

tff(c_16,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_43,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_49,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_555,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_relset_1(A_95,B_96,C_97) = k2_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_559,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_555])).

tff(c_771,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1(k2_relset_1(A_115,B_116,C_117),k1_zfmisc_1(B_116))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_784,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_771])).

tff(c_789,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_784])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_475,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_750,plain,(
    ! [A_110,B_111,A_112] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_112)
      | ~ m1_subset_1(A_110,k1_zfmisc_1(A_112))
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_475])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_761,plain,(
    ! [A_110,A_112] :
      ( ~ m1_subset_1(A_110,k1_zfmisc_1(A_112))
      | r1_tarski(A_110,A_112) ) ),
    inference(resolution,[status(thm)],[c_750,c_4])).

tff(c_796,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_789,c_761])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_807,plain,(
    k2_xboole_0(k2_relat_1('#skF_5'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_796,c_10])).

tff(c_61,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,(
    ! [A_56,B_57] : r1_tarski(A_56,k2_xboole_0(A_56,B_57)) ),
    inference(resolution,[status(thm)],[c_67,c_8])).

tff(c_118,plain,(
    ! [A_6,B_7,B_57] : r1_tarski(A_6,k2_xboole_0(k2_xboole_0(A_6,B_7),B_57)) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_345,plain,(
    ! [A_73,B_74] :
      ( k8_relat_1(A_73,B_74) = B_74
      | ~ r1_tarski(k2_relat_1(B_74),A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_363,plain,(
    ! [B_74,B_7,B_57] :
      ( k8_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(B_74),B_7),B_57),B_74) = B_74
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_118,c_345])).

tff(c_843,plain,(
    ! [B_57] :
      ( k8_relat_1(k2_xboole_0('#skF_3',B_57),'#skF_5') = '#skF_5'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_363])).

tff(c_871,plain,(
    ! [B_118] : k8_relat_1(k2_xboole_0('#skF_3',B_118),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_843])).

tff(c_891,plain,(
    k8_relat_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_871])).

tff(c_900,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k6_relset_1(A_119,B_120,C_121,D_122) = k8_relat_1(C_121,D_122)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_907,plain,(
    ! [C_121] : k6_relset_1('#skF_2','#skF_3',C_121,'#skF_5') = k8_relat_1(C_121,'#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_900])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k6_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_981,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k8_relat_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_28])).

tff(c_982,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_981])).

tff(c_1032,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( r2_relset_1(A_127,B_128,C_129,C_129)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1120,plain,(
    ! [C_134] :
      ( r2_relset_1('#skF_2','#skF_3',C_134,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_1032])).

tff(c_1125,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_1120])).

tff(c_1130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:52:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.46  
% 2.99/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.46  %$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.99/1.46  
% 2.99/1.46  %Foreground sorts:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Background operators:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Foreground operators:
% 2.99/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.99/1.46  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.99/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.46  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.99/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.46  
% 2.99/1.47  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.99/1.47  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.99/1.47  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.99/1.47  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.99/1.47  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.99/1.47  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.99/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.99/1.47  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.99/1.47  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.99/1.47  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.99/1.47  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.99/1.47  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.99/1.47  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.47  tff(c_34, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.99/1.47  tff(c_38, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_30, c_34])).
% 2.99/1.47  tff(c_16, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.47  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.47  tff(c_43, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.99/1.47  tff(c_46, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_43])).
% 2.99/1.47  tff(c_49, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46])).
% 2.99/1.47  tff(c_555, plain, (![A_95, B_96, C_97]: (k2_relset_1(A_95, B_96, C_97)=k2_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.47  tff(c_559, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_555])).
% 2.99/1.47  tff(c_771, plain, (![A_115, B_116, C_117]: (m1_subset_1(k2_relset_1(A_115, B_116, C_117), k1_zfmisc_1(B_116)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.99/1.47  tff(c_784, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_559, c_771])).
% 2.99/1.47  tff(c_789, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_784])).
% 2.99/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.47  tff(c_475, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.99/1.47  tff(c_750, plain, (![A_110, B_111, A_112]: (r2_hidden('#skF_1'(A_110, B_111), A_112) | ~m1_subset_1(A_110, k1_zfmisc_1(A_112)) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_6, c_475])).
% 2.99/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.47  tff(c_761, plain, (![A_110, A_112]: (~m1_subset_1(A_110, k1_zfmisc_1(A_112)) | r1_tarski(A_110, A_112))), inference(resolution, [status(thm)], [c_750, c_4])).
% 2.99/1.47  tff(c_796, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_789, c_761])).
% 2.99/1.47  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.99/1.47  tff(c_807, plain, (k2_xboole_0(k2_relat_1('#skF_5'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_796, c_10])).
% 2.99/1.47  tff(c_61, plain, (![A_49, B_50]: (~r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.47  tff(c_67, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_6, c_61])).
% 2.99/1.47  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.99/1.47  tff(c_99, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_xboole_0(A_56, B_57)))), inference(resolution, [status(thm)], [c_67, c_8])).
% 2.99/1.47  tff(c_118, plain, (![A_6, B_7, B_57]: (r1_tarski(A_6, k2_xboole_0(k2_xboole_0(A_6, B_7), B_57)))), inference(resolution, [status(thm)], [c_99, c_8])).
% 2.99/1.47  tff(c_345, plain, (![A_73, B_74]: (k8_relat_1(A_73, B_74)=B_74 | ~r1_tarski(k2_relat_1(B_74), A_73) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.47  tff(c_363, plain, (![B_74, B_7, B_57]: (k8_relat_1(k2_xboole_0(k2_xboole_0(k2_relat_1(B_74), B_7), B_57), B_74)=B_74 | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_118, c_345])).
% 2.99/1.47  tff(c_843, plain, (![B_57]: (k8_relat_1(k2_xboole_0('#skF_3', B_57), '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_807, c_363])).
% 2.99/1.47  tff(c_871, plain, (![B_118]: (k8_relat_1(k2_xboole_0('#skF_3', B_118), '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_843])).
% 2.99/1.47  tff(c_891, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_38, c_871])).
% 2.99/1.47  tff(c_900, plain, (![A_119, B_120, C_121, D_122]: (k6_relset_1(A_119, B_120, C_121, D_122)=k8_relat_1(C_121, D_122) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.99/1.47  tff(c_907, plain, (![C_121]: (k6_relset_1('#skF_2', '#skF_3', C_121, '#skF_5')=k8_relat_1(C_121, '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_900])).
% 2.99/1.47  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_3', k6_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.99/1.47  tff(c_981, plain, (~r2_relset_1('#skF_2', '#skF_3', k8_relat_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_907, c_28])).
% 2.99/1.47  tff(c_982, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_891, c_981])).
% 2.99/1.47  tff(c_1032, plain, (![A_127, B_128, C_129, D_130]: (r2_relset_1(A_127, B_128, C_129, C_129) | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.47  tff(c_1120, plain, (![C_134]: (r2_relset_1('#skF_2', '#skF_3', C_134, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_32, c_1032])).
% 2.99/1.47  tff(c_1125, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_1120])).
% 2.99/1.47  tff(c_1130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_982, c_1125])).
% 2.99/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  Inference rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Ref     : 0
% 2.99/1.47  #Sup     : 252
% 2.99/1.47  #Fact    : 0
% 2.99/1.47  #Define  : 0
% 2.99/1.47  #Split   : 1
% 2.99/1.47  #Chain   : 0
% 2.99/1.47  #Close   : 0
% 2.99/1.47  
% 2.99/1.47  Ordering : KBO
% 2.99/1.47  
% 2.99/1.47  Simplification rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Subsume      : 13
% 2.99/1.47  #Demod        : 139
% 2.99/1.47  #Tautology    : 142
% 2.99/1.47  #SimpNegUnit  : 1
% 2.99/1.47  #BackRed      : 1
% 2.99/1.47  
% 2.99/1.47  #Partial instantiations: 0
% 2.99/1.47  #Strategies tried      : 1
% 2.99/1.47  
% 2.99/1.47  Timing (in seconds)
% 2.99/1.47  ----------------------
% 2.99/1.48  Preprocessing        : 0.29
% 2.99/1.48  Parsing              : 0.16
% 2.99/1.48  CNF conversion       : 0.02
% 2.99/1.48  Main loop            : 0.37
% 2.99/1.48  Inferencing          : 0.15
% 2.99/1.48  Reduction            : 0.12
% 2.99/1.48  Demodulation         : 0.09
% 2.99/1.48  BG Simplification    : 0.02
% 2.99/1.48  Subsumption          : 0.06
% 2.99/1.48  Abstraction          : 0.02
% 2.99/1.48  MUC search           : 0.00
% 2.99/1.48  Cooper               : 0.00
% 2.99/1.48  Total                : 0.70
% 2.99/1.48  Index Insertion      : 0.00
% 2.99/1.48  Index Deletion       : 0.00
% 2.99/1.48  Index Matching       : 0.00
% 2.99/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
