%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   58 (  81 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 121 expanded)
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

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_78,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

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

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_8,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_44,plain,(
    ! [C_33,A_34,B_35] :
      ( v4_relat_1(C_33,A_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_49,plain,(
    ! [B_36,A_37] :
      ( k7_relat_1(B_36,A_37) = B_36
      | ~ v4_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_49])).

tff(c_55,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_14,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_14])).

tff(c_63,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_59])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_28])).

tff(c_65,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_xboole_0(A_38,C_39)
      | ~ r1_xboole_0(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_45] :
      ( r1_xboole_0(A_45,'#skF_2')
      | ~ r1_tarski(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_31,c_65])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_45] :
      ( r1_xboole_0('#skF_2',A_45)
      | ~ r1_tarski(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_120,plain,(
    ! [A_52,B_53] :
      ( k7_relat_1(A_52,B_53) = k1_xboole_0
      | ~ r1_xboole_0(B_53,k1_relat_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [A_59] :
      ( k7_relat_1(A_59,'#skF_2') = k1_xboole_0
      | ~ v1_relat_1(A_59)
      | ~ r1_tarski(k1_relat_1(A_59),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_90,c_120])).

tff(c_165,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_162])).

tff(c_172,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_165])).

tff(c_193,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k5_relset_1(A_60,B_61,C_62,D_63) = k7_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_196,plain,(
    ! [D_63] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_63) = k7_relat_1('#skF_4',D_63) ),
    inference(resolution,[status(thm)],[c_26,c_193])).

tff(c_22,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_199,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_22])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:28:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.27  
% 2.14/1.27  %Foreground sorts:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Background operators:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Foreground operators:
% 2.14/1.27  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.27  
% 2.14/1.28  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.14/1.28  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 2.14/1.28  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.14/1.28  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.28  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.14/1.28  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.14/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.14/1.28  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.14/1.28  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.14/1.28  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.14/1.28  tff(c_8, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.28  tff(c_32, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.14/1.28  tff(c_35, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_32])).
% 2.14/1.28  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_35])).
% 2.14/1.28  tff(c_44, plain, (![C_33, A_34, B_35]: (v4_relat_1(C_33, A_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.28  tff(c_48, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.14/1.28  tff(c_49, plain, (![B_36, A_37]: (k7_relat_1(B_36, A_37)=B_36 | ~v4_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.28  tff(c_52, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_49])).
% 2.14/1.28  tff(c_55, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.14/1.28  tff(c_14, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.28  tff(c_59, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_55, c_14])).
% 2.14/1.28  tff(c_63, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_59])).
% 2.14/1.28  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.28  tff(c_28, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.28  tff(c_31, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_28])).
% 2.14/1.28  tff(c_65, plain, (![A_38, C_39, B_40]: (r1_xboole_0(A_38, C_39) | ~r1_xboole_0(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.28  tff(c_84, plain, (![A_45]: (r1_xboole_0(A_45, '#skF_2') | ~r1_tarski(A_45, '#skF_3'))), inference(resolution, [status(thm)], [c_31, c_65])).
% 2.14/1.28  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.28  tff(c_90, plain, (![A_45]: (r1_xboole_0('#skF_2', A_45) | ~r1_tarski(A_45, '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_2])).
% 2.14/1.28  tff(c_120, plain, (![A_52, B_53]: (k7_relat_1(A_52, B_53)=k1_xboole_0 | ~r1_xboole_0(B_53, k1_relat_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.28  tff(c_162, plain, (![A_59]: (k7_relat_1(A_59, '#skF_2')=k1_xboole_0 | ~v1_relat_1(A_59) | ~r1_tarski(k1_relat_1(A_59), '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_120])).
% 2.14/1.28  tff(c_165, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_162])).
% 2.14/1.28  tff(c_172, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_165])).
% 2.14/1.28  tff(c_193, plain, (![A_60, B_61, C_62, D_63]: (k5_relset_1(A_60, B_61, C_62, D_63)=k7_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.14/1.28  tff(c_196, plain, (![D_63]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_63)=k7_relat_1('#skF_4', D_63))), inference(resolution, [status(thm)], [c_26, c_193])).
% 2.14/1.28  tff(c_22, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.28  tff(c_199, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_196, c_22])).
% 2.14/1.28  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_199])).
% 2.14/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  Inference rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Ref     : 0
% 2.14/1.28  #Sup     : 41
% 2.14/1.28  #Fact    : 0
% 2.14/1.28  #Define  : 0
% 2.14/1.28  #Split   : 4
% 2.14/1.28  #Chain   : 0
% 2.14/1.28  #Close   : 0
% 2.14/1.28  
% 2.14/1.28  Ordering : KBO
% 2.14/1.28  
% 2.14/1.28  Simplification rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Subsume      : 4
% 2.14/1.28  #Demod        : 8
% 2.14/1.28  #Tautology    : 5
% 2.14/1.28  #SimpNegUnit  : 0
% 2.14/1.28  #BackRed      : 1
% 2.14/1.28  
% 2.14/1.28  #Partial instantiations: 0
% 2.14/1.28  #Strategies tried      : 1
% 2.14/1.28  
% 2.14/1.28  Timing (in seconds)
% 2.14/1.28  ----------------------
% 2.14/1.28  Preprocessing        : 0.31
% 2.14/1.28  Parsing              : 0.16
% 2.14/1.28  CNF conversion       : 0.02
% 2.14/1.28  Main loop            : 0.20
% 2.14/1.28  Inferencing          : 0.07
% 2.14/1.28  Reduction            : 0.05
% 2.14/1.28  Demodulation         : 0.04
% 2.14/1.28  BG Simplification    : 0.01
% 2.14/1.28  Subsumption          : 0.05
% 2.14/1.28  Abstraction          : 0.01
% 2.14/1.28  MUC search           : 0.00
% 2.14/1.28  Cooper               : 0.00
% 2.14/1.28  Total                : 0.54
% 2.14/1.28  Index Insertion      : 0.00
% 2.14/1.28  Index Deletion       : 0.00
% 2.14/1.28  Index Matching       : 0.00
% 2.14/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
