%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:06 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   66 (  98 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 146 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_51,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_57,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_57])).

tff(c_101,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_110,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_101])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_364,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_373,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_364])).

tff(c_465,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1(k1_relset_1(A_122,B_123,C_124),k1_zfmisc_1(A_122))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_486,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_465])).

tff(c_493,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_486])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_501,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_493,c_14])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_143,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_155,plain,(
    ! [A_68,A_9,B_10] :
      ( r1_tarski(A_68,k2_xboole_0(A_9,B_10))
      | ~ r1_tarski(A_68,A_9) ) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_24,plain,(
    ! [A_23] :
      ( k2_xboole_0(k1_relat_1(A_23),k2_relat_1(A_23)) = k3_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_263,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(k2_xboole_0(A_86,C_87),B_88)
      | ~ r1_tarski(C_87,B_88)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1061,plain,(
    ! [A_220,B_221] :
      ( r1_tarski(k3_relat_1(A_220),B_221)
      | ~ r1_tarski(k2_relat_1(A_220),B_221)
      | ~ r1_tarski(k1_relat_1(A_220),B_221)
      | ~ v1_relat_1(A_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_263])).

tff(c_36,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1118,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1061,c_36])).

tff(c_1141,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1118])).

tff(c_1149,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_1158,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_1149])).

tff(c_1167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_1158])).

tff(c_1168,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_1183,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_1168])).

tff(c_1186,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1183])).

tff(c_1190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_110,c_1186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  
% 3.58/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.59  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.58/1.59  
% 3.58/1.59  %Foreground sorts:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Background operators:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Foreground operators:
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.59  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.58/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.58/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.58/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.58/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.58/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.58/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.58/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.58/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.59  
% 3.58/1.60  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.58/1.60  tff(f_89, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.58/1.60  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.58/1.60  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.58/1.60  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.58/1.60  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.58/1.60  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.58/1.60  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.58/1.60  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.58/1.60  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.58/1.60  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.58/1.60  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.58/1.60  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.58/1.60  tff(c_26, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.58/1.60  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.58/1.60  tff(c_51, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.58/1.60  tff(c_57, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_51])).
% 3.58/1.60  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_57])).
% 3.58/1.60  tff(c_101, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.58/1.60  tff(c_110, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_101])).
% 3.58/1.60  tff(c_22, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.58/1.60  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.60  tff(c_364, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.58/1.60  tff(c_373, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_364])).
% 3.58/1.60  tff(c_465, plain, (![A_122, B_123, C_124]: (m1_subset_1(k1_relset_1(A_122, B_123, C_124), k1_zfmisc_1(A_122)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.58/1.60  tff(c_486, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_373, c_465])).
% 3.58/1.60  tff(c_493, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_486])).
% 3.58/1.60  tff(c_14, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.58/1.60  tff(c_501, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_493, c_14])).
% 3.58/1.60  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.60  tff(c_143, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.60  tff(c_155, plain, (![A_68, A_9, B_10]: (r1_tarski(A_68, k2_xboole_0(A_9, B_10)) | ~r1_tarski(A_68, A_9))), inference(resolution, [status(thm)], [c_8, c_143])).
% 3.58/1.60  tff(c_24, plain, (![A_23]: (k2_xboole_0(k1_relat_1(A_23), k2_relat_1(A_23))=k3_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.60  tff(c_263, plain, (![A_86, C_87, B_88]: (r1_tarski(k2_xboole_0(A_86, C_87), B_88) | ~r1_tarski(C_87, B_88) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.58/1.60  tff(c_1061, plain, (![A_220, B_221]: (r1_tarski(k3_relat_1(A_220), B_221) | ~r1_tarski(k2_relat_1(A_220), B_221) | ~r1_tarski(k1_relat_1(A_220), B_221) | ~v1_relat_1(A_220))), inference(superposition, [status(thm), theory('equality')], [c_24, c_263])).
% 3.58/1.60  tff(c_36, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.58/1.60  tff(c_1118, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1061, c_36])).
% 3.58/1.60  tff(c_1141, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1118])).
% 3.58/1.60  tff(c_1149, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1141])).
% 3.58/1.60  tff(c_1158, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_155, c_1149])).
% 3.58/1.60  tff(c_1167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_1158])).
% 3.58/1.60  tff(c_1168, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1141])).
% 3.58/1.60  tff(c_1183, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_4, c_1168])).
% 3.58/1.60  tff(c_1186, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_1183])).
% 3.58/1.60  tff(c_1190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_110, c_1186])).
% 3.58/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.60  
% 3.58/1.60  Inference rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Ref     : 0
% 3.58/1.60  #Sup     : 271
% 3.58/1.60  #Fact    : 0
% 3.58/1.60  #Define  : 0
% 3.58/1.60  #Split   : 8
% 3.58/1.60  #Chain   : 0
% 3.58/1.60  #Close   : 0
% 3.58/1.60  
% 3.58/1.60  Ordering : KBO
% 3.58/1.60  
% 3.58/1.60  Simplification rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Subsume      : 38
% 3.58/1.60  #Demod        : 31
% 3.58/1.60  #Tautology    : 23
% 3.58/1.60  #SimpNegUnit  : 0
% 3.58/1.60  #BackRed      : 0
% 3.58/1.60  
% 3.58/1.60  #Partial instantiations: 0
% 3.58/1.60  #Strategies tried      : 1
% 3.58/1.60  
% 3.58/1.60  Timing (in seconds)
% 3.58/1.60  ----------------------
% 3.58/1.61  Preprocessing        : 0.32
% 3.58/1.61  Parsing              : 0.17
% 3.58/1.61  CNF conversion       : 0.02
% 3.58/1.61  Main loop            : 0.52
% 3.58/1.61  Inferencing          : 0.19
% 3.58/1.61  Reduction            : 0.14
% 3.58/1.61  Demodulation         : 0.10
% 3.58/1.61  BG Simplification    : 0.02
% 3.58/1.61  Subsumption          : 0.12
% 3.58/1.61  Abstraction          : 0.02
% 3.58/1.61  MUC search           : 0.00
% 3.58/1.61  Cooper               : 0.00
% 3.58/1.61  Total                : 0.87
% 3.58/1.61  Index Insertion      : 0.00
% 3.58/1.61  Index Deletion       : 0.00
% 3.58/1.61  Index Matching       : 0.00
% 3.58/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
