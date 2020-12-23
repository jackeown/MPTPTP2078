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
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 115 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_203,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k5_relset_1(A_64,B_65,C_66,D_67) = k7_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_206,plain,(
    ! [D_67] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_67) = k7_relat_1('#skF_4',D_67) ),
    inference(resolution,[status(thm)],[c_28,c_203])).

tff(c_24,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_207,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_24])).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_45,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_42])).

tff(c_81,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_91,plain,(
    ! [B_45,A_46] :
      ( k7_relat_1(B_45,A_46) = B_45
      | ~ v4_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_91])).

tff(c_97,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_94])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_12])).

tff(c_109,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_105])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(B_26,A_27)
      | ~ r1_xboole_0(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_46,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_xboole_0(A_32,C_33)
      | ~ r1_xboole_0(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_32] :
      ( r1_xboole_0(A_32,'#skF_2')
      | ~ r1_tarski(A_32,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_33,c_46])).

tff(c_156,plain,(
    ! [B_59,A_60] :
      ( k7_relat_1(B_59,A_60) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_217,plain,(
    ! [B_69] :
      ( k7_relat_1(B_69,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_69)
      | ~ r1_tarski(k1_relat_1(B_69),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_51,c_156])).

tff(c_220,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_217])).

tff(c_227,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_220])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.25  
% 2.17/1.26  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.17/1.26  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.17/1.26  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.26  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.26  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.17/1.26  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.17/1.26  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.17/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.17/1.26  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.17/1.26  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.17/1.26  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.17/1.26  tff(c_203, plain, (![A_64, B_65, C_66, D_67]: (k5_relset_1(A_64, B_65, C_66, D_67)=k7_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.26  tff(c_206, plain, (![D_67]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_67)=k7_relat_1('#skF_4', D_67))), inference(resolution, [status(thm)], [c_28, c_203])).
% 2.17/1.26  tff(c_24, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.17/1.26  tff(c_207, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_206, c_24])).
% 2.17/1.26  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.26  tff(c_39, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.26  tff(c_42, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_39])).
% 2.17/1.26  tff(c_45, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_42])).
% 2.17/1.26  tff(c_81, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.26  tff(c_85, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.17/1.26  tff(c_91, plain, (![B_45, A_46]: (k7_relat_1(B_45, A_46)=B_45 | ~v4_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.26  tff(c_94, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_85, c_91])).
% 2.17/1.26  tff(c_97, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_94])).
% 2.17/1.26  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.26  tff(c_105, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_97, c_12])).
% 2.17/1.26  tff(c_109, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_105])).
% 2.17/1.26  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.17/1.26  tff(c_30, plain, (![B_26, A_27]: (r1_xboole_0(B_26, A_27) | ~r1_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.26  tff(c_33, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_30])).
% 2.17/1.26  tff(c_46, plain, (![A_32, C_33, B_34]: (r1_xboole_0(A_32, C_33) | ~r1_xboole_0(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.26  tff(c_51, plain, (![A_32]: (r1_xboole_0(A_32, '#skF_2') | ~r1_tarski(A_32, '#skF_3'))), inference(resolution, [status(thm)], [c_33, c_46])).
% 2.17/1.26  tff(c_156, plain, (![B_59, A_60]: (k7_relat_1(B_59, A_60)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.26  tff(c_217, plain, (![B_69]: (k7_relat_1(B_69, '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_69) | ~r1_tarski(k1_relat_1(B_69), '#skF_3'))), inference(resolution, [status(thm)], [c_51, c_156])).
% 2.17/1.26  tff(c_220, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_109, c_217])).
% 2.17/1.26  tff(c_227, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_45, c_220])).
% 2.17/1.26  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_227])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 47
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 2
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 6
% 2.17/1.26  #Demod        : 7
% 2.17/1.26  #Tautology    : 6
% 2.17/1.26  #SimpNegUnit  : 1
% 2.17/1.26  #BackRed      : 1
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.26  
% 2.17/1.26  Timing (in seconds)
% 2.17/1.26  ----------------------
% 2.17/1.26  Preprocessing        : 0.29
% 2.17/1.26  Parsing              : 0.16
% 2.17/1.26  CNF conversion       : 0.02
% 2.17/1.26  Main loop            : 0.20
% 2.17/1.26  Inferencing          : 0.08
% 2.17/1.27  Reduction            : 0.05
% 2.17/1.27  Demodulation         : 0.03
% 2.17/1.27  BG Simplification    : 0.01
% 2.17/1.27  Subsumption          : 0.05
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.52
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
