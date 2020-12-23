%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 119 expanded)
%              Number of equality atoms :   18 (  24 expanded)
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_73,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_76,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_79,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_180,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_184,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_180])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_187,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_16])).

tff(c_190,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_187])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_19,A_18)),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_194,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_18])).

tff(c_198,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_194])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = A_31
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_36])).

tff(c_81,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_xboole_0(A_41,k4_xboole_0(C_42,B_43))
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_46] :
      ( r1_xboole_0(A_46,'#skF_2')
      | ~ r1_tarski(A_46,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_81])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_46] :
      ( r1_xboole_0('#skF_2',A_46)
      | ~ r1_tarski(A_46,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_236,plain,(
    ! [A_65,B_66] :
      ( k7_relat_1(A_65,B_66) = k1_xboole_0
      | ~ r1_xboole_0(B_66,k1_relat_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_295,plain,(
    ! [A_70] :
      ( k7_relat_1(A_70,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_70)
      | ~ r1_tarski(k1_relat_1(A_70),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_103,c_236])).

tff(c_298,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_295])).

tff(c_305,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_298])).

tff(c_352,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k5_relset_1(A_71,B_72,C_73,D_74) = k7_relat_1(C_73,D_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_355,plain,(
    ! [D_74] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_74) = k7_relat_1('#skF_4',D_74) ),
    inference(resolution,[status(thm)],[c_30,c_352])).

tff(c_26,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_381,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_26])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:48:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  
% 2.32/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.26  
% 2.32/1.26  %Foreground sorts:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Background operators:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Foreground operators:
% 2.32/1.26  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.32/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.32/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.32/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.26  
% 2.32/1.28  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.32/1.28  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.32/1.28  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.32/1.28  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.32/1.28  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.32/1.28  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.32/1.28  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.32/1.28  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.32/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.32/1.28  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.32/1.28  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.32/1.28  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.28  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.28  tff(c_73, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.28  tff(c_76, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_73])).
% 2.32/1.28  tff(c_79, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_76])).
% 2.32/1.28  tff(c_180, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.32/1.28  tff(c_184, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_180])).
% 2.32/1.28  tff(c_16, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.32/1.28  tff(c_187, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_184, c_16])).
% 2.32/1.28  tff(c_190, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_187])).
% 2.32/1.28  tff(c_18, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(k7_relat_1(B_19, A_18)), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.32/1.28  tff(c_194, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_190, c_18])).
% 2.32/1.28  tff(c_198, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_194])).
% 2.32/1.28  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.28  tff(c_36, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=A_31 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.32/1.28  tff(c_40, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_28, c_36])).
% 2.32/1.28  tff(c_81, plain, (![A_41, C_42, B_43]: (r1_xboole_0(A_41, k4_xboole_0(C_42, B_43)) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.28  tff(c_96, plain, (![A_46]: (r1_xboole_0(A_46, '#skF_2') | ~r1_tarski(A_46, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_81])).
% 2.32/1.28  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.28  tff(c_103, plain, (![A_46]: (r1_xboole_0('#skF_2', A_46) | ~r1_tarski(A_46, '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.32/1.28  tff(c_236, plain, (![A_65, B_66]: (k7_relat_1(A_65, B_66)=k1_xboole_0 | ~r1_xboole_0(B_66, k1_relat_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.32/1.28  tff(c_295, plain, (![A_70]: (k7_relat_1(A_70, '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_70) | ~r1_tarski(k1_relat_1(A_70), '#skF_3'))), inference(resolution, [status(thm)], [c_103, c_236])).
% 2.32/1.28  tff(c_298, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_198, c_295])).
% 2.32/1.28  tff(c_305, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79, c_298])).
% 2.32/1.28  tff(c_352, plain, (![A_71, B_72, C_73, D_74]: (k5_relset_1(A_71, B_72, C_73, D_74)=k7_relat_1(C_73, D_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.28  tff(c_355, plain, (![D_74]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_74)=k7_relat_1('#skF_4', D_74))), inference(resolution, [status(thm)], [c_30, c_352])).
% 2.32/1.28  tff(c_26, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.28  tff(c_381, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_355, c_26])).
% 2.32/1.28  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_305, c_381])).
% 2.32/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.28  
% 2.32/1.28  Inference rules
% 2.32/1.28  ----------------------
% 2.32/1.28  #Ref     : 0
% 2.32/1.28  #Sup     : 89
% 2.32/1.28  #Fact    : 0
% 2.32/1.28  #Define  : 0
% 2.32/1.28  #Split   : 0
% 2.32/1.28  #Chain   : 0
% 2.32/1.28  #Close   : 0
% 2.32/1.28  
% 2.32/1.28  Ordering : KBO
% 2.32/1.28  
% 2.32/1.28  Simplification rules
% 2.32/1.28  ----------------------
% 2.32/1.28  #Subsume      : 7
% 2.32/1.28  #Demod        : 16
% 2.32/1.28  #Tautology    : 26
% 2.32/1.28  #SimpNegUnit  : 0
% 2.32/1.28  #BackRed      : 1
% 2.32/1.28  
% 2.32/1.28  #Partial instantiations: 0
% 2.32/1.28  #Strategies tried      : 1
% 2.32/1.28  
% 2.32/1.28  Timing (in seconds)
% 2.32/1.28  ----------------------
% 2.32/1.28  Preprocessing        : 0.30
% 2.32/1.28  Parsing              : 0.16
% 2.32/1.28  CNF conversion       : 0.02
% 2.32/1.28  Main loop            : 0.23
% 2.32/1.28  Inferencing          : 0.09
% 2.32/1.28  Reduction            : 0.06
% 2.32/1.28  Demodulation         : 0.04
% 2.32/1.28  BG Simplification    : 0.01
% 2.32/1.28  Subsumption          : 0.04
% 2.32/1.28  Abstraction          : 0.01
% 2.32/1.28  MUC search           : 0.00
% 2.32/1.28  Cooper               : 0.00
% 2.32/1.28  Total                : 0.56
% 2.32/1.28  Index Insertion      : 0.00
% 2.32/1.28  Index Deletion       : 0.00
% 2.32/1.28  Index Matching       : 0.00
% 2.32/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
