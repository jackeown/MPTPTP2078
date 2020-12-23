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
% DateTime   : Thu Dec  3 10:08:40 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  58 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  76 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_169,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_173,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_169])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_75,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_xboole_0(A_34,k4_xboole_0(C_35,B_36))
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_37] :
      ( r1_xboole_0(A_37,'#skF_2')
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_75])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [A_37] :
      ( r1_xboole_0('#skF_2',A_37)
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_235,plain,(
    ! [A_64,B_65] :
      ( k7_relat_1(A_64,B_65) = k1_xboole_0
      | ~ r1_xboole_0(B_65,k1_relat_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_261,plain,(
    ! [A_66] :
      ( k7_relat_1(A_66,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_66)
      | ~ r1_tarski(k1_relat_1(A_66),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_96,c_235])).

tff(c_267,plain,(
    ! [B_67] :
      ( k7_relat_1(B_67,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_67,'#skF_3')
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_12,c_261])).

tff(c_270,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_267])).

tff(c_273,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_270])).

tff(c_278,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( k5_relset_1(A_68,B_69,C_70,D_71) = k7_relat_1(C_70,D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_281,plain,(
    ! [D_71] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_71) = k7_relat_1('#skF_4',D_71) ),
    inference(resolution,[status(thm)],[c_28,c_278])).

tff(c_24,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_282,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_24])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.25  
% 2.22/1.26  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 2.22/1.26  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.22/1.26  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.22/1.26  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.22/1.26  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.22/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.22/1.26  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.22/1.26  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.22/1.26  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.26  tff(c_62, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.22/1.26  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_62])).
% 2.22/1.26  tff(c_169, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.22/1.26  tff(c_173, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_169])).
% 2.22/1.26  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.26  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.26  tff(c_41, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.26  tff(c_53, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_41])).
% 2.22/1.26  tff(c_75, plain, (![A_34, C_35, B_36]: (r1_xboole_0(A_34, k4_xboole_0(C_35, B_36)) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.26  tff(c_89, plain, (![A_37]: (r1_xboole_0(A_37, '#skF_2') | ~r1_tarski(A_37, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_75])).
% 2.22/1.26  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.26  tff(c_96, plain, (![A_37]: (r1_xboole_0('#skF_2', A_37) | ~r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_89, c_2])).
% 2.22/1.26  tff(c_235, plain, (![A_64, B_65]: (k7_relat_1(A_64, B_65)=k1_xboole_0 | ~r1_xboole_0(B_65, k1_relat_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.22/1.26  tff(c_261, plain, (![A_66]: (k7_relat_1(A_66, '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_66) | ~r1_tarski(k1_relat_1(A_66), '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_235])).
% 2.22/1.26  tff(c_267, plain, (![B_67]: (k7_relat_1(B_67, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_67, '#skF_3') | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_12, c_261])).
% 2.22/1.26  tff(c_270, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_173, c_267])).
% 2.22/1.26  tff(c_273, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_270])).
% 2.22/1.26  tff(c_278, plain, (![A_68, B_69, C_70, D_71]: (k5_relset_1(A_68, B_69, C_70, D_71)=k7_relat_1(C_70, D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.22/1.26  tff(c_281, plain, (![D_71]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_71)=k7_relat_1('#skF_4', D_71))), inference(resolution, [status(thm)], [c_28, c_278])).
% 2.22/1.26  tff(c_24, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.26  tff(c_282, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_281, c_24])).
% 2.22/1.26  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_273, c_282])).
% 2.22/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  Inference rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Ref     : 0
% 2.22/1.26  #Sup     : 63
% 2.22/1.26  #Fact    : 0
% 2.22/1.26  #Define  : 0
% 2.22/1.26  #Split   : 0
% 2.22/1.26  #Chain   : 0
% 2.22/1.26  #Close   : 0
% 2.22/1.26  
% 2.22/1.26  Ordering : KBO
% 2.22/1.26  
% 2.22/1.26  Simplification rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Subsume      : 8
% 2.22/1.26  #Demod        : 6
% 2.22/1.26  #Tautology    : 15
% 2.22/1.26  #SimpNegUnit  : 0
% 2.22/1.26  #BackRed      : 1
% 2.22/1.26  
% 2.22/1.26  #Partial instantiations: 0
% 2.22/1.26  #Strategies tried      : 1
% 2.22/1.26  
% 2.22/1.26  Timing (in seconds)
% 2.22/1.26  ----------------------
% 2.22/1.26  Preprocessing        : 0.30
% 2.22/1.26  Parsing              : 0.16
% 2.22/1.26  CNF conversion       : 0.02
% 2.22/1.26  Main loop            : 0.20
% 2.22/1.26  Inferencing          : 0.08
% 2.22/1.26  Reduction            : 0.05
% 2.22/1.26  Demodulation         : 0.03
% 2.22/1.26  BG Simplification    : 0.01
% 2.22/1.26  Subsumption          : 0.04
% 2.22/1.26  Abstraction          : 0.01
% 2.22/1.26  MUC search           : 0.00
% 2.22/1.26  Cooper               : 0.00
% 2.22/1.26  Total                : 0.53
% 2.22/1.26  Index Insertion      : 0.00
% 2.22/1.26  Index Deletion       : 0.00
% 2.22/1.26  Index Matching       : 0.00
% 2.22/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
