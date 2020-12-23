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
% DateTime   : Thu Dec  3 10:07:05 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   48 (  87 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 138 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [B_20,A_21] :
      ( v1_relat_1(B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_29])).

tff(c_39,plain,(
    ! [C_27,B_28,A_29] :
      ( v5_relat_1(C_27,B_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_29,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_43,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [C_24,A_25,B_26] :
      ( v4_relat_1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_12] :
      ( k2_xboole_0(k1_relat_1(A_12),k2_relat_1(A_12)) = k3_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    ! [A_37,C_38,B_39,D_40] :
      ( r1_tarski(k2_xboole_0(A_37,C_38),k2_xboole_0(B_39,D_40))
      | ~ r1_tarski(C_38,D_40)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_41,B_42,D_43] :
      ( r1_tarski(k3_relat_1(A_41),k2_xboole_0(B_42,D_43))
      | ~ r1_tarski(k2_relat_1(A_41),D_43)
      | ~ r1_tarski(k1_relat_1(A_41),B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_22,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_74,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_22])).

tff(c_80,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_81,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_84,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38,c_84])).

tff(c_89,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_93,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_43,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.22  
% 1.81/1.22  %Foreground sorts:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Background operators:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Foreground operators:
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.22  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.81/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.81/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.81/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.22  
% 1.99/1.23  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.99/1.23  tff(f_67, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 1.99/1.23  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.99/1.23  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.99/1.23  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.99/1.23  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.99/1.23  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.99/1.23  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 1.99/1.23  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.23  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.23  tff(c_26, plain, (![B_20, A_21]: (v1_relat_1(B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.23  tff(c_29, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_26])).
% 1.99/1.23  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_29])).
% 1.99/1.23  tff(c_39, plain, (![C_27, B_28, A_29]: (v5_relat_1(C_27, B_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_29, B_28))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.23  tff(c_43, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_39])).
% 1.99/1.23  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.23  tff(c_34, plain, (![C_24, A_25, B_26]: (v4_relat_1(C_24, A_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.23  tff(c_38, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_34])).
% 1.99/1.23  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.99/1.23  tff(c_14, plain, (![A_12]: (k2_xboole_0(k1_relat_1(A_12), k2_relat_1(A_12))=k3_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.23  tff(c_64, plain, (![A_37, C_38, B_39, D_40]: (r1_tarski(k2_xboole_0(A_37, C_38), k2_xboole_0(B_39, D_40)) | ~r1_tarski(C_38, D_40) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.23  tff(c_71, plain, (![A_41, B_42, D_43]: (r1_tarski(k3_relat_1(A_41), k2_xboole_0(B_42, D_43)) | ~r1_tarski(k2_relat_1(A_41), D_43) | ~r1_tarski(k1_relat_1(A_41), B_42) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_14, c_64])).
% 1.99/1.23  tff(c_22, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.23  tff(c_74, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_22])).
% 1.99/1.23  tff(c_80, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 1.99/1.23  tff(c_81, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_80])).
% 1.99/1.23  tff(c_84, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_81])).
% 1.99/1.23  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_38, c_84])).
% 1.99/1.23  tff(c_89, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 1.99/1.23  tff(c_93, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_89])).
% 1.99/1.23  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_43, c_93])).
% 1.99/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  Inference rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Ref     : 0
% 1.99/1.23  #Sup     : 13
% 1.99/1.23  #Fact    : 0
% 1.99/1.23  #Define  : 0
% 1.99/1.23  #Split   : 1
% 1.99/1.23  #Chain   : 0
% 1.99/1.23  #Close   : 0
% 1.99/1.23  
% 1.99/1.23  Ordering : KBO
% 1.99/1.23  
% 1.99/1.23  Simplification rules
% 1.99/1.23  ----------------------
% 1.99/1.23  #Subsume      : 0
% 1.99/1.23  #Demod        : 6
% 1.99/1.23  #Tautology    : 4
% 1.99/1.23  #SimpNegUnit  : 0
% 1.99/1.23  #BackRed      : 0
% 1.99/1.23  
% 1.99/1.23  #Partial instantiations: 0
% 1.99/1.23  #Strategies tried      : 1
% 1.99/1.23  
% 1.99/1.23  Timing (in seconds)
% 1.99/1.23  ----------------------
% 1.99/1.24  Preprocessing        : 0.30
% 1.99/1.24  Parsing              : 0.17
% 1.99/1.24  CNF conversion       : 0.02
% 1.99/1.24  Main loop            : 0.13
% 1.99/1.24  Inferencing          : 0.06
% 1.99/1.24  Reduction            : 0.04
% 1.99/1.24  Demodulation         : 0.03
% 1.99/1.24  BG Simplification    : 0.01
% 1.99/1.24  Subsumption          : 0.02
% 1.99/1.24  Abstraction          : 0.00
% 1.99/1.24  MUC search           : 0.00
% 1.99/1.24  Cooper               : 0.00
% 1.99/1.24  Total                : 0.45
% 1.99/1.24  Index Insertion      : 0.00
% 1.99/1.24  Index Deletion       : 0.00
% 1.99/1.24  Index Matching       : 0.00
% 1.99/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
