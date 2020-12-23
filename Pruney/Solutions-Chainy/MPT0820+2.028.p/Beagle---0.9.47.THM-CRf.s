%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:04 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 113 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 184 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_22,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_74,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_80,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_87,plain,(
    ! [C_37,B_38,A_39] :
      ( v5_relat_1(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_87])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_81,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_81])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(k2_xboole_0(A_50,C_51),k2_xboole_0(B_52,C_51))
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k3_relat_1(A_68),k2_xboole_0(B_69,k2_relat_1(A_68)))
      | ~ r1_tarski(k1_relat_1(A_68),B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_119])).

tff(c_390,plain,(
    ! [A_90,A_91] :
      ( r1_tarski(k3_relat_1(A_90),k2_xboole_0(k2_relat_1(A_90),A_91))
      | ~ r1_tarski(k1_relat_1(A_90),A_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_163,plain,(
    ! [A_56,B_57,A_58] :
      ( r1_tarski(k2_xboole_0(A_56,B_57),k2_xboole_0(B_57,A_58))
      | ~ r1_tarski(A_56,A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_184,plain,(
    ! [A_3,B_57,A_58,A_56] :
      ( r1_tarski(A_3,k2_xboole_0(B_57,A_58))
      | ~ r1_tarski(A_3,k2_xboole_0(A_56,B_57))
      | ~ r1_tarski(A_56,A_58) ) ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_1332,plain,(
    ! [A_177,A_178,A_179] :
      ( r1_tarski(k3_relat_1(A_177),k2_xboole_0(A_178,A_179))
      | ~ r1_tarski(k2_relat_1(A_177),A_179)
      | ~ r1_tarski(k1_relat_1(A_177),A_178)
      | ~ v1_relat_1(A_177) ) ),
    inference(resolution,[status(thm)],[c_390,c_184])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1369,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1332,c_28])).

tff(c_1397,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1369])).

tff(c_1398,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1397])).

tff(c_1465,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1398])).

tff(c_1469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_85,c_1465])).

tff(c_1470,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1397])).

tff(c_1474,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1470])).

tff(c_1478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_91,c_1474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.71  
% 3.95/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.71  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.95/1.71  
% 3.95/1.71  %Foreground sorts:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Background operators:
% 3.95/1.71  
% 3.95/1.71  
% 3.95/1.71  %Foreground operators:
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.71  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.95/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.95/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.95/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.95/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.71  
% 3.95/1.72  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.95/1.72  tff(f_75, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 3.95/1.72  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.95/1.72  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.95/1.72  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.95/1.72  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.95/1.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.95/1.72  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.95/1.72  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 3.95/1.72  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.95/1.72  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.95/1.72  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.95/1.72  tff(c_74, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.95/1.72  tff(c_77, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_74])).
% 3.95/1.72  tff(c_80, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_77])).
% 3.95/1.72  tff(c_87, plain, (![C_37, B_38, A_39]: (v5_relat_1(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_38))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/1.72  tff(c_91, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_87])).
% 3.95/1.72  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.95/1.72  tff(c_81, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.95/1.72  tff(c_85, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_81])).
% 3.95/1.72  tff(c_14, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.95/1.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.95/1.72  tff(c_20, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.72  tff(c_119, plain, (![A_50, C_51, B_52]: (r1_tarski(k2_xboole_0(A_50, C_51), k2_xboole_0(B_52, C_51)) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.95/1.72  tff(c_225, plain, (![A_68, B_69]: (r1_tarski(k3_relat_1(A_68), k2_xboole_0(B_69, k2_relat_1(A_68))) | ~r1_tarski(k1_relat_1(A_68), B_69) | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_20, c_119])).
% 3.95/1.72  tff(c_390, plain, (![A_90, A_91]: (r1_tarski(k3_relat_1(A_90), k2_xboole_0(k2_relat_1(A_90), A_91)) | ~r1_tarski(k1_relat_1(A_90), A_91) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_2, c_225])).
% 3.95/1.72  tff(c_163, plain, (![A_56, B_57, A_58]: (r1_tarski(k2_xboole_0(A_56, B_57), k2_xboole_0(B_57, A_58)) | ~r1_tarski(A_56, A_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 3.95/1.72  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.95/1.72  tff(c_184, plain, (![A_3, B_57, A_58, A_56]: (r1_tarski(A_3, k2_xboole_0(B_57, A_58)) | ~r1_tarski(A_3, k2_xboole_0(A_56, B_57)) | ~r1_tarski(A_56, A_58))), inference(resolution, [status(thm)], [c_163, c_4])).
% 3.95/1.72  tff(c_1332, plain, (![A_177, A_178, A_179]: (r1_tarski(k3_relat_1(A_177), k2_xboole_0(A_178, A_179)) | ~r1_tarski(k2_relat_1(A_177), A_179) | ~r1_tarski(k1_relat_1(A_177), A_178) | ~v1_relat_1(A_177))), inference(resolution, [status(thm)], [c_390, c_184])).
% 3.95/1.72  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.95/1.72  tff(c_1369, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1332, c_28])).
% 3.95/1.72  tff(c_1397, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1369])).
% 3.95/1.72  tff(c_1398, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1397])).
% 3.95/1.72  tff(c_1465, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1398])).
% 3.95/1.72  tff(c_1469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_85, c_1465])).
% 3.95/1.72  tff(c_1470, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1397])).
% 3.95/1.72  tff(c_1474, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1470])).
% 3.95/1.72  tff(c_1478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_91, c_1474])).
% 3.95/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.72  
% 3.95/1.72  Inference rules
% 3.95/1.72  ----------------------
% 3.95/1.72  #Ref     : 0
% 3.95/1.72  #Sup     : 433
% 3.95/1.72  #Fact    : 0
% 3.95/1.72  #Define  : 0
% 3.95/1.72  #Split   : 1
% 3.95/1.72  #Chain   : 0
% 3.95/1.72  #Close   : 0
% 3.95/1.72  
% 3.95/1.72  Ordering : KBO
% 3.95/1.72  
% 3.95/1.72  Simplification rules
% 3.95/1.72  ----------------------
% 3.95/1.72  #Subsume      : 76
% 3.95/1.72  #Demod        : 10
% 3.95/1.72  #Tautology    : 19
% 3.95/1.72  #SimpNegUnit  : 0
% 3.95/1.72  #BackRed      : 0
% 3.95/1.72  
% 3.95/1.72  #Partial instantiations: 0
% 3.95/1.72  #Strategies tried      : 1
% 3.95/1.72  
% 3.95/1.72  Timing (in seconds)
% 3.95/1.72  ----------------------
% 3.95/1.73  Preprocessing        : 0.30
% 3.95/1.73  Parsing              : 0.17
% 3.95/1.73  CNF conversion       : 0.02
% 3.95/1.73  Main loop            : 0.64
% 3.95/1.73  Inferencing          : 0.17
% 3.95/1.73  Reduction            : 0.19
% 3.95/1.73  Demodulation         : 0.15
% 3.95/1.73  BG Simplification    : 0.02
% 3.95/1.73  Subsumption          : 0.20
% 3.95/1.73  Abstraction          : 0.03
% 3.95/1.73  MUC search           : 0.00
% 3.95/1.73  Cooper               : 0.00
% 3.95/1.73  Total                : 0.97
% 3.95/1.73  Index Insertion      : 0.00
% 3.95/1.73  Index Deletion       : 0.00
% 3.95/1.73  Index Matching       : 0.00
% 3.95/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
