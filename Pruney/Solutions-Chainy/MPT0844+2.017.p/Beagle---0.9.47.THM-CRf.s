%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:42 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   58 (  66 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 (  85 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_601,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k5_relset_1(A_106,B_107,C_108,D_109) = k7_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_612,plain,(
    ! [D_109] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_109) = k7_relat_1('#skF_4',D_109) ),
    inference(resolution,[status(thm)],[c_42,c_601])).

tff(c_38,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_725,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_38])).

tff(c_227,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_240,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_227])).

tff(c_24,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_73,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_89,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_89])).

tff(c_26,plain,(
    ! [A_16,C_18,B_17,D_19] : k3_xboole_0(k2_zfmisc_1(A_16,C_18),k2_zfmisc_1(B_17,D_19)) = k2_zfmisc_1(k3_xboole_0(A_16,B_17),k3_xboole_0(C_18,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_130,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_134,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_330,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_xboole_0(A_69,C_70)
      | ~ r1_xboole_0(B_71,C_70)
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_969,plain,(
    ! [A_135,B_136,A_137] :
      ( r1_xboole_0(A_135,B_136)
      | ~ r1_tarski(A_135,A_137)
      | k3_xboole_0(A_137,B_136) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_330])).

tff(c_974,plain,(
    ! [B_138] :
      ( r1_xboole_0('#skF_4',B_138)
      | k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_1'),B_138) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_134,c_969])).

tff(c_1099,plain,(
    ! [B_144,D_145] :
      ( r1_xboole_0('#skF_4',k2_zfmisc_1(B_144,D_145))
      | k2_zfmisc_1(k3_xboole_0('#skF_3',B_144),k3_xboole_0('#skF_1',D_145)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_974])).

tff(c_1118,plain,(
    ! [D_145] :
      ( r1_xboole_0('#skF_4',k2_zfmisc_1('#skF_2',D_145))
      | k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_1',D_145)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1099])).

tff(c_1133,plain,(
    ! [D_146] : r1_xboole_0('#skF_4',k2_zfmisc_1('#skF_2',D_146)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1118])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1214,plain,(
    ! [D_149] : k3_xboole_0('#skF_4',k2_zfmisc_1('#skF_2',D_149)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1133,c_2])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( k3_xboole_0(B_23,k2_zfmisc_1(A_22,k2_relat_1(B_23))) = k7_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1225,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_32])).

tff(c_1239,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_1225])).

tff(c_1241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_725,c_1239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.56  
% 3.34/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.57  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.57  
% 3.43/1.57  %Foreground sorts:
% 3.43/1.57  
% 3.43/1.57  
% 3.43/1.57  %Background operators:
% 3.43/1.57  
% 3.43/1.57  
% 3.43/1.57  %Foreground operators:
% 3.43/1.57  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.43/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.43/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.43/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.43/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.57  
% 3.43/1.58  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 3.43/1.58  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.43/1.58  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.43/1.58  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.43/1.58  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.43/1.58  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.43/1.58  tff(f_57, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.43/1.58  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.43/1.58  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.43/1.58  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 3.43/1.58  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.43/1.58  tff(c_601, plain, (![A_106, B_107, C_108, D_109]: (k5_relset_1(A_106, B_107, C_108, D_109)=k7_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.43/1.58  tff(c_612, plain, (![D_109]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_109)=k7_relat_1('#skF_4', D_109))), inference(resolution, [status(thm)], [c_42, c_601])).
% 3.43/1.58  tff(c_38, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.43/1.58  tff(c_725, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_612, c_38])).
% 3.43/1.58  tff(c_227, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.43/1.58  tff(c_240, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_227])).
% 3.43/1.58  tff(c_24, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.43/1.58  tff(c_40, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.43/1.58  tff(c_73, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.43/1.58  tff(c_79, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_73])).
% 3.43/1.58  tff(c_89, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.58  tff(c_102, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_79, c_89])).
% 3.43/1.58  tff(c_26, plain, (![A_16, C_18, B_17, D_19]: (k3_xboole_0(k2_zfmisc_1(A_16, C_18), k2_zfmisc_1(B_17, D_19))=k2_zfmisc_1(k3_xboole_0(A_16, B_17), k3_xboole_0(C_18, D_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.43/1.58  tff(c_130, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.43/1.58  tff(c_134, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_42, c_130])).
% 3.43/1.58  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.58  tff(c_330, plain, (![A_69, C_70, B_71]: (r1_xboole_0(A_69, C_70) | ~r1_xboole_0(B_71, C_70) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.58  tff(c_969, plain, (![A_135, B_136, A_137]: (r1_xboole_0(A_135, B_136) | ~r1_tarski(A_135, A_137) | k3_xboole_0(A_137, B_136)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_330])).
% 3.43/1.58  tff(c_974, plain, (![B_138]: (r1_xboole_0('#skF_4', B_138) | k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_1'), B_138)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_969])).
% 3.43/1.58  tff(c_1099, plain, (![B_144, D_145]: (r1_xboole_0('#skF_4', k2_zfmisc_1(B_144, D_145)) | k2_zfmisc_1(k3_xboole_0('#skF_3', B_144), k3_xboole_0('#skF_1', D_145))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_974])).
% 3.43/1.58  tff(c_1118, plain, (![D_145]: (r1_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', D_145)) | k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_1', D_145))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_1099])).
% 3.43/1.58  tff(c_1133, plain, (![D_146]: (r1_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', D_146)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1118])).
% 3.43/1.58  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.58  tff(c_1214, plain, (![D_149]: (k3_xboole_0('#skF_4', k2_zfmisc_1('#skF_2', D_149))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1133, c_2])).
% 3.43/1.58  tff(c_32, plain, (![B_23, A_22]: (k3_xboole_0(B_23, k2_zfmisc_1(A_22, k2_relat_1(B_23)))=k7_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.43/1.58  tff(c_1225, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1214, c_32])).
% 3.43/1.58  tff(c_1239, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_240, c_1225])).
% 3.43/1.58  tff(c_1241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_725, c_1239])).
% 3.43/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.58  
% 3.43/1.58  Inference rules
% 3.43/1.58  ----------------------
% 3.43/1.58  #Ref     : 0
% 3.43/1.58  #Sup     : 289
% 3.43/1.58  #Fact    : 0
% 3.43/1.58  #Define  : 0
% 3.43/1.58  #Split   : 5
% 3.43/1.58  #Chain   : 0
% 3.43/1.58  #Close   : 0
% 3.43/1.58  
% 3.43/1.58  Ordering : KBO
% 3.43/1.58  
% 3.43/1.58  Simplification rules
% 3.43/1.58  ----------------------
% 3.43/1.58  #Subsume      : 20
% 3.43/1.58  #Demod        : 114
% 3.43/1.58  #Tautology    : 150
% 3.43/1.58  #SimpNegUnit  : 1
% 3.43/1.58  #BackRed      : 1
% 3.43/1.58  
% 3.43/1.58  #Partial instantiations: 0
% 3.43/1.58  #Strategies tried      : 1
% 3.43/1.58  
% 3.43/1.58  Timing (in seconds)
% 3.43/1.58  ----------------------
% 3.43/1.58  Preprocessing        : 0.34
% 3.43/1.58  Parsing              : 0.18
% 3.43/1.58  CNF conversion       : 0.02
% 3.43/1.58  Main loop            : 0.43
% 3.43/1.58  Inferencing          : 0.16
% 3.43/1.58  Reduction            : 0.13
% 3.43/1.58  Demodulation         : 0.09
% 3.43/1.58  BG Simplification    : 0.02
% 3.43/1.58  Subsumption          : 0.09
% 3.43/1.58  Abstraction          : 0.02
% 3.43/1.58  MUC search           : 0.00
% 3.43/1.58  Cooper               : 0.00
% 3.43/1.58  Total                : 0.80
% 3.43/1.58  Index Insertion      : 0.00
% 3.43/1.58  Index Deletion       : 0.00
% 3.43/1.58  Index Matching       : 0.00
% 3.43/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
