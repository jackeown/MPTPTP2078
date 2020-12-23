%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:05 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  81 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 124 expanded)
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

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_52,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_24,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_43,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_49,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_69,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_73,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_16,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(k2_xboole_0(A_52,C_53),k2_xboole_0(B_54,C_53))
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [A_22,B_54] :
      ( r1_tarski(k3_relat_1(A_22),k2_xboole_0(B_54,k2_relat_1(A_22)))
      | ~ r1_tarski(k1_relat_1(A_22),B_54)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_60,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_60])).

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
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_61,A_62,B_63] :
      ( r1_tarski(A_61,A_62)
      | ~ r1_tarski(A_61,k2_relat_1(B_63))
      | ~ v5_relat_1(B_63,A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_623,plain,(
    ! [A_159,B_160,A_161,B_162] :
      ( r1_tarski(k4_xboole_0(A_159,B_160),A_161)
      | ~ v5_relat_1(B_162,A_161)
      | ~ v1_relat_1(B_162)
      | ~ r1_tarski(A_159,k2_xboole_0(B_160,k2_relat_1(B_162))) ) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_625,plain,(
    ! [A_159,B_160] :
      ( r1_tarski(k4_xboole_0(A_159,B_160),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_159,k2_xboole_0(B_160,k2_relat_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_64,c_623])).

tff(c_629,plain,(
    ! [A_163,B_164] :
      ( r1_tarski(k4_xboole_0(A_163,B_164),'#skF_2')
      | ~ r1_tarski(A_163,k2_xboole_0(B_164,k2_relat_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_625])).

tff(c_633,plain,(
    ! [B_54] :
      ( r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'),B_54),'#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_54)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_93,c_629])).

tff(c_692,plain,(
    ! [B_167] :
      ( r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'),B_167),'#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_633])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(A_7,k2_xboole_0(B_8,C_9))
      | ~ r1_tarski(k4_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_738,plain,(
    ! [B_169] :
      ( r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0(B_169,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_169) ) ),
    inference(resolution,[status(thm)],[c_692,c_6])).

tff(c_30,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_769,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_738,c_30])).

tff(c_772,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_769])).

tff(c_776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_73,c_772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.52  
% 3.06/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.52  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.06/1.52  
% 3.06/1.52  %Foreground sorts:
% 3.06/1.52  
% 3.06/1.52  
% 3.06/1.52  %Background operators:
% 3.06/1.52  
% 3.06/1.52  
% 3.06/1.52  %Foreground operators:
% 3.06/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.52  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.06/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.06/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.06/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.06/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.52  
% 3.37/1.54  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.37/1.54  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 3.37/1.54  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.37/1.54  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.37/1.54  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.37/1.54  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.37/1.54  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 3.37/1.54  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.37/1.54  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.37/1.54  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.37/1.54  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.37/1.54  tff(c_24, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.54  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.54  tff(c_43, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.37/1.54  tff(c_46, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_43])).
% 3.37/1.54  tff(c_49, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_46])).
% 3.37/1.54  tff(c_69, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.37/1.54  tff(c_73, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_69])).
% 3.37/1.54  tff(c_16, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.37/1.54  tff(c_22, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.54  tff(c_88, plain, (![A_52, C_53, B_54]: (r1_tarski(k2_xboole_0(A_52, C_53), k2_xboole_0(B_54, C_53)) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.37/1.54  tff(c_93, plain, (![A_22, B_54]: (r1_tarski(k3_relat_1(A_22), k2_xboole_0(B_54, k2_relat_1(A_22))) | ~r1_tarski(k1_relat_1(A_22), B_54) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_22, c_88])).
% 3.37/1.54  tff(c_60, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.37/1.54  tff(c_64, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_60])).
% 3.37/1.54  tff(c_4, plain, (![A_4, B_5, C_6]: (r1_tarski(k4_xboole_0(A_4, B_5), C_6) | ~r1_tarski(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.37/1.54  tff(c_65, plain, (![B_41, A_42]: (r1_tarski(k2_relat_1(B_41), A_42) | ~v5_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.37/1.54  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.37/1.54  tff(c_107, plain, (![A_61, A_62, B_63]: (r1_tarski(A_61, A_62) | ~r1_tarski(A_61, k2_relat_1(B_63)) | ~v5_relat_1(B_63, A_62) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_65, c_2])).
% 3.37/1.54  tff(c_623, plain, (![A_159, B_160, A_161, B_162]: (r1_tarski(k4_xboole_0(A_159, B_160), A_161) | ~v5_relat_1(B_162, A_161) | ~v1_relat_1(B_162) | ~r1_tarski(A_159, k2_xboole_0(B_160, k2_relat_1(B_162))))), inference(resolution, [status(thm)], [c_4, c_107])).
% 3.37/1.54  tff(c_625, plain, (![A_159, B_160]: (r1_tarski(k4_xboole_0(A_159, B_160), '#skF_2') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_159, k2_xboole_0(B_160, k2_relat_1('#skF_3'))))), inference(resolution, [status(thm)], [c_64, c_623])).
% 3.37/1.54  tff(c_629, plain, (![A_163, B_164]: (r1_tarski(k4_xboole_0(A_163, B_164), '#skF_2') | ~r1_tarski(A_163, k2_xboole_0(B_164, k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_625])).
% 3.37/1.54  tff(c_633, plain, (![B_54]: (r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'), B_54), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), B_54) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_93, c_629])).
% 3.37/1.54  tff(c_692, plain, (![B_167]: (r1_tarski(k4_xboole_0(k3_relat_1('#skF_3'), B_167), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), B_167))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_633])).
% 3.37/1.54  tff(c_6, plain, (![A_7, B_8, C_9]: (r1_tarski(A_7, k2_xboole_0(B_8, C_9)) | ~r1_tarski(k4_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.54  tff(c_738, plain, (![B_169]: (r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0(B_169, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), B_169))), inference(resolution, [status(thm)], [c_692, c_6])).
% 3.37/1.54  tff(c_30, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.54  tff(c_769, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_738, c_30])).
% 3.37/1.54  tff(c_772, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_769])).
% 3.37/1.54  tff(c_776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_73, c_772])).
% 3.37/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.54  
% 3.37/1.54  Inference rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Ref     : 0
% 3.37/1.54  #Sup     : 194
% 3.37/1.54  #Fact    : 0
% 3.37/1.54  #Define  : 0
% 3.37/1.54  #Split   : 0
% 3.37/1.54  #Chain   : 0
% 3.37/1.54  #Close   : 0
% 3.37/1.54  
% 3.37/1.54  Ordering : KBO
% 3.37/1.54  
% 3.37/1.54  Simplification rules
% 3.37/1.54  ----------------------
% 3.37/1.54  #Subsume      : 8
% 3.37/1.54  #Demod        : 12
% 3.37/1.54  #Tautology    : 9
% 3.37/1.54  #SimpNegUnit  : 0
% 3.37/1.54  #BackRed      : 0
% 3.37/1.54  
% 3.37/1.54  #Partial instantiations: 0
% 3.37/1.54  #Strategies tried      : 1
% 3.37/1.54  
% 3.37/1.54  Timing (in seconds)
% 3.37/1.54  ----------------------
% 3.37/1.54  Preprocessing        : 0.28
% 3.37/1.54  Parsing              : 0.16
% 3.37/1.54  CNF conversion       : 0.02
% 3.37/1.54  Main loop            : 0.43
% 3.37/1.54  Inferencing          : 0.16
% 3.37/1.54  Reduction            : 0.10
% 3.37/1.54  Demodulation         : 0.07
% 3.37/1.54  BG Simplification    : 0.02
% 3.37/1.54  Subsumption          : 0.11
% 3.37/1.54  Abstraction          : 0.02
% 3.37/1.54  MUC search           : 0.00
% 3.37/1.54  Cooper               : 0.00
% 3.37/1.54  Total                : 0.74
% 3.37/1.54  Index Insertion      : 0.00
% 3.37/1.54  Index Deletion       : 0.00
% 3.37/1.54  Index Matching       : 0.00
% 3.37/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
