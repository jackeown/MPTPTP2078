%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:37 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 (  92 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_106,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_relset_1(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_106])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_59,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k1_relat_1(B_42),A_43)
      | ~ v4_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    ! [B_51,A_52] :
      ( k2_xboole_0(k1_relat_1(B_51),A_52) = A_52
      | ~ v4_relat_1(B_51,A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [B_56,C_57,A_58] :
      ( r1_tarski(k1_relat_1(B_56),C_57)
      | ~ r1_tarski(A_58,C_57)
      | ~ v4_relat_1(B_56,A_58)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2])).

tff(c_120,plain,(
    ! [B_59] :
      ( r1_tarski(k1_relat_1(B_59),'#skF_3')
      | ~ v4_relat_1(B_59,'#skF_2')
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_28,c_110])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_157,plain,(
    ! [B_66] :
      ( k7_relat_1(B_66,'#skF_3') = B_66
      | ~ v4_relat_1(B_66,'#skF_2')
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_120,c_14])).

tff(c_160,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_157])).

tff(c_163,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_160])).

tff(c_136,plain,(
    ! [A_60,B_61,C_62,D_63] :
      ( k5_relset_1(A_60,B_61,C_62,D_63) = k7_relat_1(C_62,D_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_139,plain,(
    ! [D_63] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_63) = k7_relat_1('#skF_4',D_63) ),
    inference(resolution,[status(thm)],[c_30,c_136])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_140,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_26])).

tff(c_170,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_140])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.22  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.22  
% 2.05/1.22  %Foreground sorts:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Background operators:
% 2.05/1.22  
% 2.05/1.22  
% 2.05/1.22  %Foreground operators:
% 2.05/1.22  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.05/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.05/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.05/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.05/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.22  
% 2.07/1.24  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.07/1.24  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.07/1.24  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.07/1.24  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.07/1.24  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.07/1.24  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.07/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.07/1.24  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.07/1.24  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.07/1.24  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.07/1.24  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.24  tff(c_106, plain, (![A_53, B_54, D_55]: (r2_relset_1(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.24  tff(c_109, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_106])).
% 2.07/1.24  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.24  tff(c_51, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.07/1.24  tff(c_54, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.07/1.24  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 2.07/1.24  tff(c_59, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.24  tff(c_63, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_59])).
% 2.07/1.24  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.24  tff(c_64, plain, (![B_42, A_43]: (r1_tarski(k1_relat_1(B_42), A_43) | ~v4_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.24  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.24  tff(c_94, plain, (![B_51, A_52]: (k2_xboole_0(k1_relat_1(B_51), A_52)=A_52 | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_64, c_4])).
% 2.07/1.24  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.24  tff(c_110, plain, (![B_56, C_57, A_58]: (r1_tarski(k1_relat_1(B_56), C_57) | ~r1_tarski(A_58, C_57) | ~v4_relat_1(B_56, A_58) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_94, c_2])).
% 2.07/1.24  tff(c_120, plain, (![B_59]: (r1_tarski(k1_relat_1(B_59), '#skF_3') | ~v4_relat_1(B_59, '#skF_2') | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_28, c_110])).
% 2.07/1.24  tff(c_14, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.07/1.24  tff(c_157, plain, (![B_66]: (k7_relat_1(B_66, '#skF_3')=B_66 | ~v4_relat_1(B_66, '#skF_2') | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_120, c_14])).
% 2.07/1.24  tff(c_160, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_157])).
% 2.07/1.24  tff(c_163, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_160])).
% 2.07/1.24  tff(c_136, plain, (![A_60, B_61, C_62, D_63]: (k5_relset_1(A_60, B_61, C_62, D_63)=k7_relat_1(C_62, D_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.07/1.24  tff(c_139, plain, (![D_63]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_63)=k7_relat_1('#skF_4', D_63))), inference(resolution, [status(thm)], [c_30, c_136])).
% 2.07/1.24  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.24  tff(c_140, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_26])).
% 2.07/1.24  tff(c_170, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_140])).
% 2.07/1.24  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_170])).
% 2.07/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  Inference rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Ref     : 0
% 2.07/1.24  #Sup     : 31
% 2.07/1.24  #Fact    : 0
% 2.07/1.24  #Define  : 0
% 2.07/1.24  #Split   : 0
% 2.07/1.24  #Chain   : 0
% 2.07/1.24  #Close   : 0
% 2.07/1.24  
% 2.07/1.24  Ordering : KBO
% 2.07/1.24  
% 2.07/1.24  Simplification rules
% 2.07/1.24  ----------------------
% 2.07/1.24  #Subsume      : 0
% 2.07/1.24  #Demod        : 8
% 2.07/1.24  #Tautology    : 9
% 2.07/1.24  #SimpNegUnit  : 0
% 2.07/1.24  #BackRed      : 2
% 2.07/1.24  
% 2.07/1.24  #Partial instantiations: 0
% 2.07/1.24  #Strategies tried      : 1
% 2.07/1.24  
% 2.07/1.24  Timing (in seconds)
% 2.07/1.24  ----------------------
% 2.07/1.24  Preprocessing        : 0.30
% 2.07/1.24  Parsing              : 0.16
% 2.07/1.24  CNF conversion       : 0.02
% 2.07/1.24  Main loop            : 0.17
% 2.07/1.24  Inferencing          : 0.06
% 2.07/1.24  Reduction            : 0.06
% 2.07/1.24  Demodulation         : 0.04
% 2.07/1.24  BG Simplification    : 0.01
% 2.07/1.24  Subsumption          : 0.03
% 2.07/1.24  Abstraction          : 0.01
% 2.07/1.24  MUC search           : 0.00
% 2.07/1.24  Cooper               : 0.00
% 2.07/1.24  Total                : 0.50
% 2.07/1.24  Index Insertion      : 0.00
% 2.07/1.24  Index Deletion       : 0.00
% 2.07/1.24  Index Matching       : 0.00
% 2.07/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
