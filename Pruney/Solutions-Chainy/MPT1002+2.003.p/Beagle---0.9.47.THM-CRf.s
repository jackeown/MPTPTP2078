%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:57 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 127 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 290 expanded)
%              Number of equality atoms :   28 (  95 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_84,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_84])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_369,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k8_relset_1(A_75,B_76,C_77,D_78) = k10_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_380,plain,(
    ! [D_78] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_78) = k10_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_42,c_369])).

tff(c_597,plain,(
    ! [B_134,A_135,C_136] :
      ( k1_xboole_0 = B_134
      | k8_relset_1(A_135,B_134,C_136,B_134) = A_135
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134)))
      | ~ v1_funct_2(C_136,A_135,B_134)
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_602,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_597])).

tff(c_610,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_4','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_380,c_602])).

tff(c_611,plain,(
    k10_relat_1('#skF_4','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_610])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k10_relat_1(B_12,A_11),k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_190,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [A_54,B_12,A_11] :
      ( r1_tarski(A_54,k1_relat_1(B_12))
      | ~ r1_tarski(A_54,k10_relat_1(B_12,A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_190])).

tff(c_624,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_54,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_201])).

tff(c_662,plain,(
    ! [A_139] :
      ( r1_tarski(A_139,k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_139,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_624])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,k10_relat_1(B_14,k9_relat_1(B_14,A_13)))
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_427,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_438,plain,(
    ! [D_98] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_98) = k9_relat_1('#skF_4',D_98) ),
    inference(resolution,[status(thm)],[c_42,c_427])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_381,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_36])).

tff(c_439,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_381])).

tff(c_451,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_439])).

tff(c_454,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_451])).

tff(c_665,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_662,c_454])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_665])).

tff(c_680,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_684,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_10])).

tff(c_743,plain,(
    ! [B_151,A_152] :
      ( B_151 = A_152
      | ~ r1_tarski(B_151,A_152)
      | ~ r1_tarski(A_152,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_753,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_743])).

tff(c_765,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_753])).

tff(c_681,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_689,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_681])).

tff(c_719,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_689,c_36])).

tff(c_766,plain,(
    ~ r1_tarski('#skF_1',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_765,c_719])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.50  
% 2.96/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.50  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.50  
% 2.96/1.50  %Foreground sorts:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Background operators:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Foreground operators:
% 2.96/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.96/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.96/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.96/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.96/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.50  
% 3.12/1.51  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_2)).
% 3.12/1.51  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.12/1.51  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.12/1.51  tff(f_83, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 3.12/1.51  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.12/1.51  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.12/1.51  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.12/1.51  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.12/1.51  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.12/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.12/1.51  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.51  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.51  tff(c_84, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.12/1.51  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_84])).
% 3.12/1.51  tff(c_38, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.51  tff(c_73, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 3.12/1.51  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.51  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.51  tff(c_369, plain, (![A_75, B_76, C_77, D_78]: (k8_relset_1(A_75, B_76, C_77, D_78)=k10_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.12/1.51  tff(c_380, plain, (![D_78]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_78)=k10_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_42, c_369])).
% 3.12/1.51  tff(c_597, plain, (![B_134, A_135, C_136]: (k1_xboole_0=B_134 | k8_relset_1(A_135, B_134, C_136, B_134)=A_135 | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))) | ~v1_funct_2(C_136, A_135, B_134) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.12/1.51  tff(c_602, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_597])).
% 3.12/1.51  tff(c_610, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_4', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_380, c_602])).
% 3.12/1.51  tff(c_611, plain, (k10_relat_1('#skF_4', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_73, c_610])).
% 3.12/1.51  tff(c_22, plain, (![B_12, A_11]: (r1_tarski(k10_relat_1(B_12, A_11), k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.12/1.51  tff(c_190, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.51  tff(c_201, plain, (![A_54, B_12, A_11]: (r1_tarski(A_54, k1_relat_1(B_12)) | ~r1_tarski(A_54, k10_relat_1(B_12, A_11)) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_22, c_190])).
% 3.12/1.51  tff(c_624, plain, (![A_54]: (r1_tarski(A_54, k1_relat_1('#skF_4')) | ~r1_tarski(A_54, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_611, c_201])).
% 3.12/1.51  tff(c_662, plain, (![A_139]: (r1_tarski(A_139, k1_relat_1('#skF_4')) | ~r1_tarski(A_139, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_624])).
% 3.12/1.51  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(A_13, k10_relat_1(B_14, k9_relat_1(B_14, A_13))) | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.12/1.51  tff(c_427, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.12/1.51  tff(c_438, plain, (![D_98]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_98)=k9_relat_1('#skF_4', D_98))), inference(resolution, [status(thm)], [c_42, c_427])).
% 3.12/1.51  tff(c_36, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.12/1.51  tff(c_381, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_36])).
% 3.12/1.51  tff(c_439, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_438, c_381])).
% 3.12/1.51  tff(c_451, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_439])).
% 3.12/1.51  tff(c_454, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_451])).
% 3.12/1.51  tff(c_665, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_662, c_454])).
% 3.12/1.51  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_665])).
% 3.12/1.51  tff(c_680, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_38])).
% 3.12/1.51  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.51  tff(c_684, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_10])).
% 3.12/1.51  tff(c_743, plain, (![B_151, A_152]: (B_151=A_152 | ~r1_tarski(B_151, A_152) | ~r1_tarski(A_152, B_151))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.51  tff(c_753, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_743])).
% 3.12/1.51  tff(c_765, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_684, c_753])).
% 3.12/1.51  tff(c_681, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 3.12/1.51  tff(c_689, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_680, c_681])).
% 3.12/1.51  tff(c_719, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_689, c_36])).
% 3.12/1.51  tff(c_766, plain, (~r1_tarski('#skF_1', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_765, c_719])).
% 3.12/1.51  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_684, c_766])).
% 3.12/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.51  
% 3.12/1.51  Inference rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Ref     : 0
% 3.12/1.51  #Sup     : 164
% 3.12/1.51  #Fact    : 0
% 3.12/1.51  #Define  : 0
% 3.12/1.51  #Split   : 5
% 3.12/1.51  #Chain   : 0
% 3.12/1.51  #Close   : 0
% 3.12/1.51  
% 3.12/1.51  Ordering : KBO
% 3.12/1.51  
% 3.12/1.51  Simplification rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Subsume      : 19
% 3.12/1.51  #Demod        : 67
% 3.12/1.51  #Tautology    : 78
% 3.12/1.51  #SimpNegUnit  : 1
% 3.12/1.51  #BackRed      : 8
% 3.12/1.51  
% 3.12/1.51  #Partial instantiations: 0
% 3.12/1.51  #Strategies tried      : 1
% 3.12/1.51  
% 3.12/1.51  Timing (in seconds)
% 3.12/1.51  ----------------------
% 3.12/1.52  Preprocessing        : 0.33
% 3.12/1.52  Parsing              : 0.18
% 3.12/1.52  CNF conversion       : 0.02
% 3.12/1.52  Main loop            : 0.35
% 3.12/1.52  Inferencing          : 0.13
% 3.12/1.52  Reduction            : 0.11
% 3.12/1.52  Demodulation         : 0.08
% 3.12/1.52  BG Simplification    : 0.02
% 3.12/1.52  Subsumption          : 0.07
% 3.12/1.52  Abstraction          : 0.02
% 3.12/1.52  MUC search           : 0.00
% 3.12/1.52  Cooper               : 0.00
% 3.12/1.52  Total                : 0.71
% 3.12/1.52  Index Insertion      : 0.00
% 3.12/1.52  Index Deletion       : 0.00
% 3.12/1.52  Index Matching       : 0.00
% 3.12/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
