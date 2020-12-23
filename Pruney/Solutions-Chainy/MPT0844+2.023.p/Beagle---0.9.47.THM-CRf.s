%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   51 (  57 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 (  78 expanded)
%              Number of equality atoms :   12 (  16 expanded)
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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_42,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_37])).

tff(c_46,plain,(
    ! [C_30,A_31,B_32] :
      ( v4_relat_1(C_30,A_31)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_30])).

tff(c_51,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_xboole_0(A_33,C_34)
      | ~ r1_xboole_0(B_35,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_33] :
      ( r1_xboole_0(A_33,'#skF_2')
      | ~ r1_tarski(A_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_33,c_51])).

tff(c_125,plain,(
    ! [B_55,A_56] :
      ( k7_relat_1(B_55,A_56) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_55),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_169,plain,(
    ! [B_61] :
      ( k7_relat_1(B_61,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(B_61)
      | ~ r1_tarski(k1_relat_1(B_61),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_175,plain,(
    ! [B_62] :
      ( k7_relat_1(B_62,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_62,'#skF_3')
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_178,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_175])).

tff(c_181,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_178])).

tff(c_193,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k5_relset_1(A_65,B_66,C_67,D_68) = k7_relat_1(C_67,D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_196,plain,(
    ! [D_68] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_68) = k7_relat_1('#skF_4',D_68) ),
    inference(resolution,[status(thm)],[c_28,c_193])).

tff(c_24,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_197,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_24])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.34  
% 2.04/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.34  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.04/1.34  
% 2.04/1.34  %Foreground sorts:
% 2.04/1.34  
% 2.04/1.34  
% 2.04/1.34  %Background operators:
% 2.04/1.34  
% 2.04/1.34  
% 2.04/1.34  %Foreground operators:
% 2.04/1.34  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.04/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.04/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.04/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.04/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.34  
% 2.28/1.35  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.28/1.35  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 2.28/1.35  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.28/1.35  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.28/1.35  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.28/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.28/1.35  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.28/1.35  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.28/1.35  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.28/1.35  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.35  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.35  tff(c_34, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.35  tff(c_37, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_34])).
% 2.28/1.35  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_37])).
% 2.28/1.35  tff(c_46, plain, (![C_30, A_31, B_32]: (v4_relat_1(C_30, A_31) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_50, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.28/1.35  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.35  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.35  tff(c_30, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.35  tff(c_33, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_30])).
% 2.28/1.35  tff(c_51, plain, (![A_33, C_34, B_35]: (r1_xboole_0(A_33, C_34) | ~r1_xboole_0(B_35, C_34) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.35  tff(c_56, plain, (![A_33]: (r1_xboole_0(A_33, '#skF_2') | ~r1_tarski(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_33, c_51])).
% 2.28/1.35  tff(c_125, plain, (![B_55, A_56]: (k7_relat_1(B_55, A_56)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_55), A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.35  tff(c_169, plain, (![B_61]: (k7_relat_1(B_61, '#skF_2')=k1_xboole_0 | ~v1_relat_1(B_61) | ~r1_tarski(k1_relat_1(B_61), '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_125])).
% 2.28/1.35  tff(c_175, plain, (![B_62]: (k7_relat_1(B_62, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_62, '#skF_3') | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_10, c_169])).
% 2.28/1.35  tff(c_178, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_175])).
% 2.28/1.35  tff(c_181, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_178])).
% 2.28/1.35  tff(c_193, plain, (![A_65, B_66, C_67, D_68]: (k5_relset_1(A_65, B_66, C_67, D_68)=k7_relat_1(C_67, D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.35  tff(c_196, plain, (![D_68]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_68)=k7_relat_1('#skF_4', D_68))), inference(resolution, [status(thm)], [c_28, c_193])).
% 2.28/1.35  tff(c_24, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.28/1.35  tff(c_197, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_196, c_24])).
% 2.28/1.35  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_197])).
% 2.28/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  Inference rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Ref     : 0
% 2.28/1.35  #Sup     : 39
% 2.28/1.35  #Fact    : 0
% 2.28/1.35  #Define  : 0
% 2.28/1.35  #Split   : 1
% 2.28/1.35  #Chain   : 0
% 2.28/1.35  #Close   : 0
% 2.28/1.35  
% 2.28/1.35  Ordering : KBO
% 2.28/1.35  
% 2.28/1.35  Simplification rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Subsume      : 5
% 2.28/1.35  #Demod        : 6
% 2.28/1.35  #Tautology    : 5
% 2.28/1.35  #SimpNegUnit  : 0
% 2.28/1.35  #BackRed      : 1
% 2.28/1.35  
% 2.28/1.35  #Partial instantiations: 0
% 2.28/1.35  #Strategies tried      : 1
% 2.28/1.35  
% 2.28/1.35  Timing (in seconds)
% 2.28/1.35  ----------------------
% 2.28/1.35  Preprocessing        : 0.29
% 2.28/1.35  Parsing              : 0.16
% 2.28/1.35  CNF conversion       : 0.02
% 2.28/1.35  Main loop            : 0.19
% 2.28/1.35  Inferencing          : 0.07
% 2.28/1.35  Reduction            : 0.05
% 2.28/1.35  Demodulation         : 0.03
% 2.28/1.35  BG Simplification    : 0.01
% 2.28/1.35  Subsumption          : 0.05
% 2.28/1.35  Abstraction          : 0.01
% 2.28/1.35  MUC search           : 0.00
% 2.28/1.35  Cooper               : 0.00
% 2.28/1.35  Total                : 0.50
% 2.28/1.35  Index Insertion      : 0.00
% 2.28/1.35  Index Deletion       : 0.00
% 2.28/1.35  Index Matching       : 0.00
% 2.28/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
