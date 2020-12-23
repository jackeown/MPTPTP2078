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
% DateTime   : Thu Dec  3 10:08:42 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  86 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_374,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k5_relset_1(A_106,B_107,C_108,D_109) = k7_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_381,plain,(
    ! [D_109] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_109) = k7_relat_1('#skF_4',D_109) ),
    inference(resolution,[status(thm)],[c_28,c_374])).

tff(c_24,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_406,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_24])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(B_23,A_24)
      | ~ r1_xboole_0(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_80,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_80])).

tff(c_157,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( ~ r1_xboole_0(A_52,B_53)
      | r1_xboole_0(k2_zfmisc_1(A_52,C_54),k2_zfmisc_1(B_53,D_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_269,plain,(
    ! [A_92,C_93,B_94,D_95] :
      ( k3_xboole_0(k2_zfmisc_1(A_92,C_93),k2_zfmisc_1(B_94,D_95)) = k1_xboole_0
      | ~ r1_xboole_0(A_92,B_94) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_62,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_xboole_0(A_38,C_39)
      | ~ r1_xboole_0(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_70,B_71,A_72] :
      ( r1_xboole_0(A_70,B_71)
      | ~ r1_tarski(A_70,A_72)
      | k3_xboole_0(A_72,B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_223,plain,(
    ! [B_71] :
      ( r1_xboole_0('#skF_4',B_71)
      | k3_xboole_0(k2_zfmisc_1('#skF_3','#skF_1'),B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_220])).

tff(c_299,plain,(
    ! [B_96,D_97] :
      ( r1_xboole_0('#skF_4',k2_zfmisc_1(B_96,D_97))
      | ~ r1_xboole_0('#skF_3',B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_223])).

tff(c_344,plain,(
    ! [B_104,D_105] :
      ( k3_xboole_0('#skF_4',k2_zfmisc_1(B_104,D_105)) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_104) ) ),
    inference(resolution,[status(thm)],[c_299,c_2])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(B_15,k2_zfmisc_1(A_14,k2_relat_1(B_15))) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_351,plain,(
    ! [B_104] :
      ( k7_relat_1('#skF_4',B_104) = k1_xboole_0
      | ~ v1_relat_1('#skF_4')
      | ~ r1_xboole_0('#skF_3',B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_18])).

tff(c_454,plain,(
    ! [B_115] :
      ( k7_relat_1('#skF_4',B_115) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_351])).

tff(c_484,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_454])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n025.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 10:48:05 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.42  
% 2.68/1.42  %Foreground sorts:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Background operators:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Foreground operators:
% 2.68/1.42  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.68/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.42  
% 2.68/1.43  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 2.68/1.43  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.68/1.43  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.68/1.43  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.68/1.43  tff(f_45, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.68/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.68/1.43  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.68/1.43  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.68/1.43  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 2.68/1.43  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.43  tff(c_374, plain, (![A_106, B_107, C_108, D_109]: (k5_relset_1(A_106, B_107, C_108, D_109)=k7_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.43  tff(c_381, plain, (![D_109]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_109)=k7_relat_1('#skF_4', D_109))), inference(resolution, [status(thm)], [c_28, c_374])).
% 2.68/1.43  tff(c_24, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.43  tff(c_406, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_381, c_24])).
% 2.68/1.43  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.43  tff(c_29, plain, (![B_23, A_24]: (r1_xboole_0(B_23, A_24) | ~r1_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.68/1.43  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.68/1.43  tff(c_80, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.68/1.43  tff(c_89, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_80])).
% 2.68/1.43  tff(c_157, plain, (![A_52, B_53, C_54, D_55]: (~r1_xboole_0(A_52, B_53) | r1_xboole_0(k2_zfmisc_1(A_52, C_54), k2_zfmisc_1(B_53, D_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.43  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.43  tff(c_269, plain, (![A_92, C_93, B_94, D_95]: (k3_xboole_0(k2_zfmisc_1(A_92, C_93), k2_zfmisc_1(B_94, D_95))=k1_xboole_0 | ~r1_xboole_0(A_92, B_94))), inference(resolution, [status(thm)], [c_157, c_2])).
% 2.68/1.43  tff(c_62, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.43  tff(c_66, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_62])).
% 2.68/1.43  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.43  tff(c_90, plain, (![A_38, C_39, B_40]: (r1_xboole_0(A_38, C_39) | ~r1_xboole_0(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.43  tff(c_220, plain, (![A_70, B_71, A_72]: (r1_xboole_0(A_70, B_71) | ~r1_tarski(A_70, A_72) | k3_xboole_0(A_72, B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_90])).
% 2.68/1.43  tff(c_223, plain, (![B_71]: (r1_xboole_0('#skF_4', B_71) | k3_xboole_0(k2_zfmisc_1('#skF_3', '#skF_1'), B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_220])).
% 2.68/1.43  tff(c_299, plain, (![B_96, D_97]: (r1_xboole_0('#skF_4', k2_zfmisc_1(B_96, D_97)) | ~r1_xboole_0('#skF_3', B_96))), inference(superposition, [status(thm), theory('equality')], [c_269, c_223])).
% 2.68/1.43  tff(c_344, plain, (![B_104, D_105]: (k3_xboole_0('#skF_4', k2_zfmisc_1(B_104, D_105))=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_104))), inference(resolution, [status(thm)], [c_299, c_2])).
% 2.68/1.43  tff(c_18, plain, (![B_15, A_14]: (k3_xboole_0(B_15, k2_zfmisc_1(A_14, k2_relat_1(B_15)))=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.43  tff(c_351, plain, (![B_104]: (k7_relat_1('#skF_4', B_104)=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_xboole_0('#skF_3', B_104))), inference(superposition, [status(thm), theory('equality')], [c_344, c_18])).
% 2.68/1.43  tff(c_454, plain, (![B_115]: (k7_relat_1('#skF_4', B_115)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_115))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_351])).
% 2.68/1.43  tff(c_484, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_454])).
% 2.68/1.43  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_406, c_484])).
% 2.68/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  Inference rules
% 2.68/1.43  ----------------------
% 2.68/1.43  #Ref     : 0
% 2.68/1.43  #Sup     : 113
% 2.68/1.43  #Fact    : 0
% 2.68/1.43  #Define  : 0
% 2.68/1.43  #Split   : 4
% 2.68/1.43  #Chain   : 0
% 2.68/1.43  #Close   : 0
% 2.68/1.43  
% 2.68/1.43  Ordering : KBO
% 2.68/1.43  
% 2.68/1.43  Simplification rules
% 2.68/1.43  ----------------------
% 2.68/1.43  #Subsume      : 15
% 2.68/1.43  #Demod        : 7
% 2.68/1.43  #Tautology    : 22
% 2.68/1.43  #SimpNegUnit  : 2
% 2.68/1.43  #BackRed      : 1
% 2.68/1.43  
% 2.68/1.43  #Partial instantiations: 0
% 2.68/1.43  #Strategies tried      : 1
% 2.68/1.43  
% 2.68/1.43  Timing (in seconds)
% 2.68/1.43  ----------------------
% 2.68/1.44  Preprocessing        : 0.32
% 2.68/1.44  Parsing              : 0.17
% 2.68/1.44  CNF conversion       : 0.02
% 2.68/1.44  Main loop            : 0.29
% 2.68/1.44  Inferencing          : 0.12
% 2.68/1.44  Reduction            : 0.07
% 2.68/1.44  Demodulation         : 0.04
% 2.68/1.44  BG Simplification    : 0.02
% 2.68/1.44  Subsumption          : 0.08
% 2.68/1.44  Abstraction          : 0.01
% 2.68/1.44  MUC search           : 0.00
% 2.68/1.44  Cooper               : 0.00
% 2.68/1.44  Total                : 0.64
% 2.68/1.44  Index Insertion      : 0.00
% 2.68/1.44  Index Deletion       : 0.00
% 2.68/1.44  Index Matching       : 0.00
% 2.68/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
