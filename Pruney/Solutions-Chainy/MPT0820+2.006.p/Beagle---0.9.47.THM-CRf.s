%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:01 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 106 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_60,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(k2_xboole_0(A_49,C_50),k2_xboole_0(B_51,C_50))
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_19,B_51] :
      ( r1_tarski(k3_relat_1(A_19),k2_xboole_0(B_51,k2_relat_1(A_19)))
      | ~ r1_tarski(k1_relat_1(A_19),B_51)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_54,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(k4_xboole_0(A_4,B_5),C_6)
      | ~ r1_tarski(A_4,k2_xboole_0(B_5,C_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k2_relat_1(B_41),A_42)
      | ~ v5_relat_1(B_41,A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_58,A_59,B_60] :
      ( r1_tarski(A_58,A_59)
      | ~ r1_tarski(A_58,k2_relat_1(B_60))
      | ~ v5_relat_1(B_60,A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_522,plain,(
    ! [A_143,B_144,A_145,B_146] :
      ( r1_tarski(k4_xboole_0(A_143,B_144),A_145)
      | ~ v5_relat_1(B_146,A_145)
      | ~ v1_relat_1(B_146)
      | ~ r1_tarski(A_143,k2_xboole_0(B_144,k2_relat_1(B_146))) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_524,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k4_xboole_0(A_143,B_144),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_143,k2_xboole_0(B_144,k2_relat_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_58,c_522])).

tff(c_528,plain,(
    ! [A_147,B_148] :
      ( r1_tarski(k4_xboole_0(A_147,B_148),'#skF_2')
      | ~ r1_tarski(A_147,k2_xboole_0(B_148,k2_relat_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_524])).

tff(c_536,plain,(
    ! [B_51] :
      ( r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'),B_51),'#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_51)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_88,c_528])).

tff(c_569,plain,(
    ! [B_149] :
      ( r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'),B_149),'#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_536])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(A_7,k2_xboole_0(B_8,C_9))
      | ~ r1_tarski(k4_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_636,plain,(
    ! [B_155] :
      ( r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0(B_155,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_155) ) ),
    inference(resolution,[status(thm)],[c_569,c_6])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_658,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_636,c_28])).

tff(c_661,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_658])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_64,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  
% 2.79/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.79/1.39  
% 2.79/1.39  %Foreground sorts:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Background operators:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Foreground operators:
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.79/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.79/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.39  
% 2.79/1.41  tff(f_76, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 2.79/1.41  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.41  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.41  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.79/1.41  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.79/1.41  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 2.79/1.41  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.79/1.41  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.79/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.79/1.41  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.79/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.79/1.41  tff(c_40, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.41  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_40])).
% 2.79/1.41  tff(c_60, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.41  tff(c_64, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_60])).
% 2.79/1.41  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.41  tff(c_20, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.79/1.41  tff(c_83, plain, (![A_49, C_50, B_51]: (r1_tarski(k2_xboole_0(A_49, C_50), k2_xboole_0(B_51, C_50)) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.41  tff(c_88, plain, (![A_19, B_51]: (r1_tarski(k3_relat_1(A_19), k2_xboole_0(B_51, k2_relat_1(A_19))) | ~r1_tarski(k1_relat_1(A_19), B_51) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_83])).
% 2.79/1.41  tff(c_54, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.41  tff(c_58, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_54])).
% 2.79/1.41  tff(c_4, plain, (![A_4, B_5, C_6]: (r1_tarski(k4_xboole_0(A_4, B_5), C_6) | ~r1_tarski(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.41  tff(c_65, plain, (![B_41, A_42]: (r1_tarski(k2_relat_1(B_41), A_42) | ~v5_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.41  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.41  tff(c_102, plain, (![A_58, A_59, B_60]: (r1_tarski(A_58, A_59) | ~r1_tarski(A_58, k2_relat_1(B_60)) | ~v5_relat_1(B_60, A_59) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.79/1.41  tff(c_522, plain, (![A_143, B_144, A_145, B_146]: (r1_tarski(k4_xboole_0(A_143, B_144), A_145) | ~v5_relat_1(B_146, A_145) | ~v1_relat_1(B_146) | ~r1_tarski(A_143, k2_xboole_0(B_144, k2_relat_1(B_146))))), inference(resolution, [status(thm)], [c_4, c_102])).
% 2.79/1.41  tff(c_524, plain, (![A_143, B_144]: (r1_tarski(k4_xboole_0(A_143, B_144), '#skF_2') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_143, k2_xboole_0(B_144, k2_relat_1('#skF_3'))))), inference(resolution, [status(thm)], [c_58, c_522])).
% 2.79/1.41  tff(c_528, plain, (![A_147, B_148]: (r1_tarski(k4_xboole_0(A_147, B_148), '#skF_2') | ~r1_tarski(A_147, k2_xboole_0(B_148, k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_524])).
% 2.79/1.41  tff(c_536, plain, (![B_51]: (r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'), B_51), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), B_51) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_88, c_528])).
% 2.79/1.41  tff(c_569, plain, (![B_149]: (r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'), B_149), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), B_149))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_536])).
% 2.79/1.41  tff(c_6, plain, (![A_7, B_8, C_9]: (r1_tarski(A_7, k2_xboole_0(B_8, C_9)) | ~r1_tarski(k4_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.41  tff(c_636, plain, (![B_155]: (r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0(B_155, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_155))), inference(resolution, [status(thm)], [c_569, c_6])).
% 2.79/1.41  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.79/1.41  tff(c_658, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_636, c_28])).
% 2.79/1.41  tff(c_661, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_658])).
% 2.79/1.41  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_64, c_661])).
% 2.79/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  Inference rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Ref     : 0
% 2.79/1.41  #Sup     : 158
% 2.79/1.41  #Fact    : 0
% 2.79/1.41  #Define  : 0
% 2.79/1.41  #Split   : 0
% 2.79/1.41  #Chain   : 0
% 2.79/1.41  #Close   : 0
% 2.79/1.41  
% 2.79/1.41  Ordering : KBO
% 2.79/1.41  
% 2.79/1.41  Simplification rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Subsume      : 5
% 2.79/1.41  #Demod        : 11
% 2.79/1.41  #Tautology    : 11
% 2.79/1.41  #SimpNegUnit  : 0
% 2.79/1.41  #BackRed      : 0
% 2.79/1.41  
% 2.79/1.41  #Partial instantiations: 0
% 2.79/1.41  #Strategies tried      : 1
% 2.79/1.41  
% 2.79/1.41  Timing (in seconds)
% 2.79/1.41  ----------------------
% 2.79/1.41  Preprocessing        : 0.28
% 2.79/1.41  Parsing              : 0.16
% 2.79/1.41  CNF conversion       : 0.02
% 2.79/1.41  Main loop            : 0.37
% 2.79/1.41  Inferencing          : 0.15
% 2.79/1.41  Reduction            : 0.08
% 2.79/1.41  Demodulation         : 0.05
% 2.79/1.41  BG Simplification    : 0.02
% 2.79/1.41  Subsumption          : 0.09
% 2.79/1.41  Abstraction          : 0.02
% 2.79/1.41  MUC search           : 0.00
% 2.79/1.41  Cooper               : 0.00
% 2.79/1.41  Total                : 0.68
% 2.79/1.41  Index Insertion      : 0.00
% 2.79/1.41  Index Deletion       : 0.00
% 2.79/1.41  Index Matching       : 0.00
% 2.79/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
