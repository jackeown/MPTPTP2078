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
% DateTime   : Thu Dec  3 10:07:02 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 (  93 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ! [C_32,A_33,B_34] :
      ( v1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_101,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_110,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_12])).

tff(c_116,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_113])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_14])).

tff(c_124,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_120])).

tff(c_126,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_135,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_176,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k2_relset_1(A_74,B_75,C_76),k1_zfmisc_1(B_75))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_176])).

tff(c_205,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_198])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_205,c_6])).

tff(c_10,plain,(
    ! [A_9] :
      ( k2_xboole_0(k1_relat_1(A_9),k2_relat_1(A_9)) = k3_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_158,plain,(
    ! [A_67,C_68,B_69,D_70] :
      ( r1_tarski(k2_xboole_0(A_67,C_68),k2_xboole_0(B_69,D_70))
      | ~ r1_tarski(C_68,D_70)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_290,plain,(
    ! [A_106,B_107,D_108] :
      ( r1_tarski(k3_relat_1(A_106),k2_xboole_0(B_107,D_108))
      | ~ r1_tarski(k2_relat_1(A_106),D_108)
      | ~ r1_tarski(k1_relat_1(A_106),B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_158])).

tff(c_26,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_293,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_26])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_124,c_209,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.33  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.26/1.33  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.26/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.26/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.26/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.33  
% 2.26/1.34  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 2.26/1.34  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.26/1.34  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.26/1.34  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.26/1.34  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.26/1.34  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.26/1.34  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.26/1.34  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.26/1.34  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.26/1.34  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 2.26/1.34  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.26/1.34  tff(c_48, plain, (![C_32, A_33, B_34]: (v1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.26/1.34  tff(c_57, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_48])).
% 2.26/1.34  tff(c_101, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.26/1.34  tff(c_110, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_101])).
% 2.26/1.34  tff(c_12, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.34  tff(c_113, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_110, c_12])).
% 2.26/1.34  tff(c_116, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_113])).
% 2.26/1.34  tff(c_14, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.26/1.34  tff(c_120, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_14])).
% 2.26/1.34  tff(c_124, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_120])).
% 2.26/1.34  tff(c_126, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.26/1.34  tff(c_135, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_126])).
% 2.26/1.34  tff(c_176, plain, (![A_74, B_75, C_76]: (m1_subset_1(k2_relset_1(A_74, B_75, C_76), k1_zfmisc_1(B_75)) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.34  tff(c_198, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_135, c_176])).
% 2.26/1.34  tff(c_205, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_198])).
% 2.26/1.34  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.34  tff(c_209, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_205, c_6])).
% 2.26/1.34  tff(c_10, plain, (![A_9]: (k2_xboole_0(k1_relat_1(A_9), k2_relat_1(A_9))=k3_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.34  tff(c_158, plain, (![A_67, C_68, B_69, D_70]: (r1_tarski(k2_xboole_0(A_67, C_68), k2_xboole_0(B_69, D_70)) | ~r1_tarski(C_68, D_70) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.34  tff(c_290, plain, (![A_106, B_107, D_108]: (r1_tarski(k3_relat_1(A_106), k2_xboole_0(B_107, D_108)) | ~r1_tarski(k2_relat_1(A_106), D_108) | ~r1_tarski(k1_relat_1(A_106), B_107) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_10, c_158])).
% 2.26/1.34  tff(c_26, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.26/1.34  tff(c_293, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_290, c_26])).
% 2.26/1.34  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_124, c_209, c_293])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 56
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 0
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 2
% 2.26/1.34  #Demod        : 14
% 2.26/1.34  #Tautology    : 15
% 2.26/1.34  #SimpNegUnit  : 0
% 2.26/1.34  #BackRed      : 0
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.32
% 2.26/1.34  Parsing              : 0.17
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.34  Main loop            : 0.21
% 2.26/1.34  Inferencing          : 0.09
% 2.26/1.34  Reduction            : 0.06
% 2.26/1.34  Demodulation         : 0.04
% 2.26/1.34  BG Simplification    : 0.01
% 2.26/1.34  Subsumption          : 0.03
% 2.26/1.34  Abstraction          : 0.01
% 2.26/1.34  MUC search           : 0.00
% 2.26/1.34  Cooper               : 0.00
% 2.26/1.34  Total                : 0.56
% 2.26/1.34  Index Insertion      : 0.00
% 2.26/1.34  Index Deletion       : 0.00
% 2.26/1.34  Index Matching       : 0.00
% 2.26/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
