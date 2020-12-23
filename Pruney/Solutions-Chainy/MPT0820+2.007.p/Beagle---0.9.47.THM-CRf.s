%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:01 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   56 (  86 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 130 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_93,plain,(
    ! [C_46,B_47,A_48] :
      ( v5_relat_1(C_46,B_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_93])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_102,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_98])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_103,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(k2_xboole_0(A_52,C_53),k2_xboole_0(B_54,C_53))
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(k2_xboole_0(A_4,B_5),C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_52,B_54,C_53] :
      ( r1_tarski(A_52,k2_xboole_0(B_54,C_53))
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_20,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_234,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(k2_xboole_0(A_72,C_73),B_74)
      | ~ r1_tarski(C_73,B_74)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_770,plain,(
    ! [A_158,B_159] :
      ( r1_tarski(k3_relat_1(A_158),B_159)
      | ~ r1_tarski(k2_relat_1(A_158),B_159)
      | ~ r1_tarski(k1_relat_1(A_158),B_159)
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_234])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_782,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_770,c_28])).

tff(c_792,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_782])).

tff(c_800,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_792])).

tff(c_822,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_113,c_800])).

tff(c_829,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_822])).

tff(c_833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_102,c_829])).

tff(c_834,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_792])).

tff(c_849,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_834])).

tff(c_864,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_849])).

tff(c_868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_97,c_864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.45  
% 3.23/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.45  
% 3.23/1.45  %Foreground sorts:
% 3.23/1.45  
% 3.23/1.45  
% 3.23/1.45  %Background operators:
% 3.23/1.45  
% 3.23/1.45  
% 3.23/1.45  %Foreground operators:
% 3.23/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.45  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.23/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.23/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.23/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.45  
% 3.23/1.46  tff(f_76, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.23/1.46  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.23/1.46  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.23/1.46  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.23/1.46  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.23/1.46  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.23/1.46  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 3.23/1.46  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.23/1.46  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.23/1.46  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.23/1.46  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.46  tff(c_36, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.46  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_36])).
% 3.23/1.46  tff(c_93, plain, (![C_46, B_47, A_48]: (v5_relat_1(C_46, B_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.46  tff(c_97, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_93])).
% 3.23/1.46  tff(c_18, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.46  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.46  tff(c_98, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.46  tff(c_102, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_98])).
% 3.23/1.46  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.46  tff(c_103, plain, (![A_52, C_53, B_54]: (r1_tarski(k2_xboole_0(A_52, C_53), k2_xboole_0(B_54, C_53)) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.46  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(k2_xboole_0(A_4, B_5), C_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.46  tff(c_113, plain, (![A_52, B_54, C_53]: (r1_tarski(A_52, k2_xboole_0(B_54, C_53)) | ~r1_tarski(A_52, B_54))), inference(resolution, [status(thm)], [c_103, c_4])).
% 3.23/1.46  tff(c_20, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.46  tff(c_234, plain, (![A_72, C_73, B_74]: (r1_tarski(k2_xboole_0(A_72, C_73), B_74) | ~r1_tarski(C_73, B_74) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.46  tff(c_770, plain, (![A_158, B_159]: (r1_tarski(k3_relat_1(A_158), B_159) | ~r1_tarski(k2_relat_1(A_158), B_159) | ~r1_tarski(k1_relat_1(A_158), B_159) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_20, c_234])).
% 3.23/1.46  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.46  tff(c_782, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_770, c_28])).
% 3.23/1.46  tff(c_792, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_782])).
% 3.23/1.46  tff(c_800, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_792])).
% 3.23/1.46  tff(c_822, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_113, c_800])).
% 3.23/1.46  tff(c_829, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_822])).
% 3.23/1.46  tff(c_833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_102, c_829])).
% 3.23/1.46  tff(c_834, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_792])).
% 3.23/1.46  tff(c_849, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_834])).
% 3.23/1.46  tff(c_864, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_849])).
% 3.23/1.46  tff(c_868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_97, c_864])).
% 3.23/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.46  
% 3.23/1.46  Inference rules
% 3.23/1.46  ----------------------
% 3.23/1.46  #Ref     : 0
% 3.23/1.46  #Sup     : 193
% 3.23/1.46  #Fact    : 0
% 3.23/1.46  #Define  : 0
% 3.23/1.47  #Split   : 2
% 3.23/1.47  #Chain   : 0
% 3.23/1.47  #Close   : 0
% 3.23/1.47  
% 3.23/1.47  Ordering : KBO
% 3.23/1.47  
% 3.23/1.47  Simplification rules
% 3.23/1.47  ----------------------
% 3.23/1.47  #Subsume      : 17
% 3.23/1.47  #Demod        : 14
% 3.23/1.47  #Tautology    : 8
% 3.23/1.47  #SimpNegUnit  : 0
% 3.23/1.47  #BackRed      : 0
% 3.23/1.47  
% 3.23/1.47  #Partial instantiations: 0
% 3.23/1.47  #Strategies tried      : 1
% 3.23/1.47  
% 3.23/1.47  Timing (in seconds)
% 3.23/1.47  ----------------------
% 3.23/1.47  Preprocessing        : 0.28
% 3.23/1.47  Parsing              : 0.16
% 3.23/1.47  CNF conversion       : 0.02
% 3.23/1.47  Main loop            : 0.42
% 3.23/1.47  Inferencing          : 0.17
% 3.23/1.47  Reduction            : 0.09
% 3.23/1.47  Demodulation         : 0.06
% 3.23/1.47  BG Simplification    : 0.02
% 3.23/1.47  Subsumption          : 0.11
% 3.23/1.47  Abstraction          : 0.02
% 3.23/1.47  MUC search           : 0.00
% 3.23/1.47  Cooper               : 0.00
% 3.23/1.47  Total                : 0.73
% 3.23/1.47  Index Insertion      : 0.00
% 3.23/1.47  Index Deletion       : 0.00
% 3.23/1.47  Index Matching       : 0.00
% 3.23/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
