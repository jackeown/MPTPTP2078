%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:06 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 146 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 243 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_343,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_352,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_343])).

tff(c_458,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1(k2_relset_1(A_116,B_117,C_118),k1_zfmisc_1(B_117))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_479,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_458])).

tff(c_486,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_479])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_494,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_486,c_12])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_49,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_59,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_55])).

tff(c_90,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_99,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_21] :
      ( k2_xboole_0(k1_relat_1(A_21),k2_relat_1(A_21)) = k3_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_252,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(k2_xboole_0(A_84,C_85),B_86)
      | ~ r1_tarski(C_85,B_86)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1142,plain,(
    ! [A_237,B_238] :
      ( r1_tarski(k3_relat_1(A_237),B_238)
      | ~ r1_tarski(k2_relat_1(A_237),B_238)
      | ~ r1_tarski(k1_relat_1(A_237),B_238)
      | ~ v1_relat_1(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_252])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_183,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(A_72,C_73)
      | ~ r1_tarski(B_74,C_73)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    ! [A_76,A_77,B_78] :
      ( r1_tarski(A_76,k2_xboole_0(A_77,B_78))
      | ~ r1_tarski(A_76,A_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_34,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_219,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_200,c_34])).

tff(c_1184,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1142,c_219])).

tff(c_1217,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1184])).

tff(c_1234,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1217])).

tff(c_1238,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1234])).

tff(c_1242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_99,c_1238])).

tff(c_1244,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_198,plain,(
    ! [A_72,A_7,B_8] :
      ( r1_tarski(A_72,k2_xboole_0(A_7,B_8))
      | ~ r1_tarski(A_72,A_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_1203,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1142,c_34])).

tff(c_1227,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1203])).

tff(c_1416,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1227])).

tff(c_1425,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_198,c_1416])).

tff(c_1437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1425])).

tff(c_1438,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1227])).

tff(c_1451,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1438])).

tff(c_1458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_1451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:34:09 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.69  
% 3.74/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.69  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.74/1.69  
% 3.74/1.69  %Foreground sorts:
% 3.74/1.69  
% 3.74/1.69  
% 3.74/1.69  %Background operators:
% 3.74/1.69  
% 3.74/1.69  
% 3.74/1.69  %Foreground operators:
% 3.74/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.74/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.74/1.69  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.74/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.74/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.74/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.74/1.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.74/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.74/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.74/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.74/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.74/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.69  
% 3.74/1.70  tff(f_87, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.74/1.70  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.74/1.70  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.74/1.70  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.74/1.70  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.74/1.70  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.74/1.70  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.74/1.70  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.74/1.70  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.74/1.70  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.74/1.70  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.74/1.70  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.74/1.70  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.74/1.70  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.74/1.70  tff(c_343, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.74/1.70  tff(c_352, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_343])).
% 3.74/1.70  tff(c_458, plain, (![A_116, B_117, C_118]: (m1_subset_1(k2_relset_1(A_116, B_117, C_118), k1_zfmisc_1(B_117)) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.74/1.70  tff(c_479, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_458])).
% 3.74/1.70  tff(c_486, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_479])).
% 3.74/1.70  tff(c_12, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.74/1.70  tff(c_494, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_486, c_12])).
% 3.74/1.70  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.74/1.70  tff(c_24, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.74/1.70  tff(c_49, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.74/1.70  tff(c_55, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_49])).
% 3.74/1.70  tff(c_59, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_55])).
% 3.74/1.70  tff(c_90, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.74/1.70  tff(c_99, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_90])).
% 3.74/1.70  tff(c_20, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.74/1.70  tff(c_22, plain, (![A_21]: (k2_xboole_0(k1_relat_1(A_21), k2_relat_1(A_21))=k3_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.74/1.70  tff(c_252, plain, (![A_84, C_85, B_86]: (r1_tarski(k2_xboole_0(A_84, C_85), B_86) | ~r1_tarski(C_85, B_86) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.74/1.70  tff(c_1142, plain, (![A_237, B_238]: (r1_tarski(k3_relat_1(A_237), B_238) | ~r1_tarski(k2_relat_1(A_237), B_238) | ~r1_tarski(k1_relat_1(A_237), B_238) | ~v1_relat_1(A_237))), inference(superposition, [status(thm), theory('equality')], [c_22, c_252])).
% 3.74/1.70  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.70  tff(c_183, plain, (![A_72, C_73, B_74]: (r1_tarski(A_72, C_73) | ~r1_tarski(B_74, C_73) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.74/1.70  tff(c_200, plain, (![A_76, A_77, B_78]: (r1_tarski(A_76, k2_xboole_0(A_77, B_78)) | ~r1_tarski(A_76, A_77))), inference(resolution, [status(thm)], [c_6, c_183])).
% 3.74/1.70  tff(c_34, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.74/1.70  tff(c_219, plain, (~r1_tarski(k3_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_200, c_34])).
% 3.74/1.70  tff(c_1184, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1142, c_219])).
% 3.74/1.70  tff(c_1217, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_1184])).
% 3.74/1.70  tff(c_1234, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1217])).
% 3.74/1.70  tff(c_1238, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1234])).
% 3.74/1.70  tff(c_1242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_99, c_1238])).
% 3.74/1.70  tff(c_1244, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_1217])).
% 3.74/1.70  tff(c_198, plain, (![A_72, A_7, B_8]: (r1_tarski(A_72, k2_xboole_0(A_7, B_8)) | ~r1_tarski(A_72, A_7))), inference(resolution, [status(thm)], [c_6, c_183])).
% 3.74/1.70  tff(c_1203, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1142, c_34])).
% 3.74/1.70  tff(c_1227, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_1203])).
% 3.74/1.70  tff(c_1416, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1227])).
% 3.74/1.70  tff(c_1425, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_198, c_1416])).
% 3.74/1.70  tff(c_1437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1425])).
% 3.74/1.70  tff(c_1438, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1227])).
% 3.74/1.70  tff(c_1451, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_1438])).
% 3.74/1.70  tff(c_1458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_494, c_1451])).
% 3.74/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.70  
% 3.74/1.70  Inference rules
% 3.74/1.70  ----------------------
% 3.74/1.70  #Ref     : 0
% 3.74/1.70  #Sup     : 342
% 3.74/1.70  #Fact    : 0
% 3.74/1.70  #Define  : 0
% 3.74/1.70  #Split   : 9
% 3.74/1.70  #Chain   : 0
% 3.74/1.70  #Close   : 0
% 3.74/1.70  
% 3.74/1.70  Ordering : KBO
% 3.74/1.70  
% 3.74/1.70  Simplification rules
% 3.74/1.70  ----------------------
% 3.74/1.70  #Subsume      : 48
% 3.74/1.70  #Demod        : 37
% 3.74/1.70  #Tautology    : 23
% 3.74/1.70  #SimpNegUnit  : 0
% 3.74/1.70  #BackRed      : 0
% 3.74/1.70  
% 3.74/1.70  #Partial instantiations: 0
% 3.74/1.70  #Strategies tried      : 1
% 3.74/1.70  
% 3.74/1.70  Timing (in seconds)
% 3.74/1.70  ----------------------
% 3.74/1.71  Preprocessing        : 0.33
% 3.74/1.71  Parsing              : 0.19
% 3.74/1.71  CNF conversion       : 0.02
% 3.74/1.71  Main loop            : 0.54
% 3.74/1.71  Inferencing          : 0.19
% 3.74/1.71  Reduction            : 0.15
% 3.74/1.71  Demodulation         : 0.10
% 3.74/1.71  BG Simplification    : 0.02
% 3.74/1.71  Subsumption          : 0.13
% 3.74/1.71  Abstraction          : 0.02
% 3.74/1.71  MUC search           : 0.00
% 3.74/1.71  Cooper               : 0.00
% 3.74/1.71  Total                : 0.90
% 3.74/1.71  Index Insertion      : 0.00
% 3.74/1.71  Index Deletion       : 0.00
% 3.74/1.71  Index Matching       : 0.00
% 3.74/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
