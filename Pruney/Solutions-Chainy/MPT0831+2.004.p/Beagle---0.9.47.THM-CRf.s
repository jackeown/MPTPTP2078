%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:33 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 112 expanded)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89,plain,(
    ! [A_48,B_49,D_50] :
      ( r2_relset_1(A_48,B_49,D_50,D_50)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_38,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_59,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k1_relat_1(B_42),A_43)
      | ~ v4_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
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

tff(c_105,plain,(
    ! [B_53,C_54,A_55] :
      ( r1_tarski(k1_relat_1(B_53),C_54)
      | ~ r1_tarski(A_55,C_54)
      | ~ v4_relat_1(B_53,A_55)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_115,plain,(
    ! [B_56] :
      ( r1_tarski(k1_relat_1(B_56),'#skF_3')
      | ~ v4_relat_1(B_56,'#skF_2')
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( v4_relat_1(B_7,A_6)
      | ~ r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [B_57] :
      ( v4_relat_1(B_57,'#skF_3')
      | ~ v4_relat_1(B_57,'#skF_2')
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_134,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_131])).

tff(c_137,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_134])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [B_44,A_45] :
      ( k7_relat_1(B_44,A_45) = B_44
      | ~ r1_tarski(k1_relat_1(B_44),A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_144,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_77])).

tff(c_147,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_144])).

tff(c_138,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k5_relset_1(A_58,B_59,C_60,D_61) = k7_relat_1(C_60,D_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,(
    ! [D_61] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_61) = k7_relat_1('#skF_4',D_61) ),
    inference(resolution,[status(thm)],[c_28,c_138])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_152,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_24])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_147,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:11:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.98/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.98/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.98/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.22  
% 1.98/1.23  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 1.98/1.23  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.98/1.23  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.98/1.23  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.98/1.23  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.98/1.23  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.98/1.23  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.98/1.23  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.98/1.23  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.98/1.23  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.23  tff(c_89, plain, (![A_48, B_49, D_50]: (r2_relset_1(A_48, B_49, D_50, D_50) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.98/1.23  tff(c_92, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_89])).
% 1.98/1.23  tff(c_38, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.23  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_38])).
% 1.98/1.23  tff(c_59, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.98/1.23  tff(c_63, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_59])).
% 1.98/1.23  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.23  tff(c_64, plain, (![B_42, A_43]: (r1_tarski(k1_relat_1(B_42), A_43) | ~v4_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.23  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.23  tff(c_93, plain, (![B_51, A_52]: (k2_xboole_0(k1_relat_1(B_51), A_52)=A_52 | ~v4_relat_1(B_51, A_52) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_64, c_4])).
% 1.98/1.23  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.23  tff(c_105, plain, (![B_53, C_54, A_55]: (r1_tarski(k1_relat_1(B_53), C_54) | ~r1_tarski(A_55, C_54) | ~v4_relat_1(B_53, A_55) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2])).
% 1.98/1.23  tff(c_115, plain, (![B_56]: (r1_tarski(k1_relat_1(B_56), '#skF_3') | ~v4_relat_1(B_56, '#skF_2') | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_26, c_105])).
% 1.98/1.23  tff(c_6, plain, (![B_7, A_6]: (v4_relat_1(B_7, A_6) | ~r1_tarski(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.23  tff(c_131, plain, (![B_57]: (v4_relat_1(B_57, '#skF_3') | ~v4_relat_1(B_57, '#skF_2') | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_115, c_6])).
% 1.98/1.23  tff(c_134, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_131])).
% 1.98/1.23  tff(c_137, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_134])).
% 1.98/1.23  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.23  tff(c_73, plain, (![B_44, A_45]: (k7_relat_1(B_44, A_45)=B_44 | ~r1_tarski(k1_relat_1(B_44), A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.23  tff(c_77, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_8, c_73])).
% 1.98/1.23  tff(c_144, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_77])).
% 1.98/1.23  tff(c_147, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_144])).
% 1.98/1.23  tff(c_138, plain, (![A_58, B_59, C_60, D_61]: (k5_relset_1(A_58, B_59, C_60, D_61)=k7_relat_1(C_60, D_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.98/1.23  tff(c_141, plain, (![D_61]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_61)=k7_relat_1('#skF_4', D_61))), inference(resolution, [status(thm)], [c_28, c_138])).
% 1.98/1.23  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.23  tff(c_152, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_24])).
% 1.98/1.23  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_147, c_152])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 30
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.23  #Split   : 0
% 1.98/1.23  #Chain   : 0
% 1.98/1.23  #Close   : 0
% 1.98/1.23  
% 1.98/1.23  Ordering : KBO
% 1.98/1.23  
% 1.98/1.23  Simplification rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Subsume      : 0
% 1.98/1.23  #Demod        : 6
% 1.98/1.23  #Tautology    : 9
% 1.98/1.23  #SimpNegUnit  : 0
% 1.98/1.23  #BackRed      : 1
% 1.98/1.23  
% 1.98/1.23  #Partial instantiations: 0
% 1.98/1.23  #Strategies tried      : 1
% 1.98/1.23  
% 1.98/1.23  Timing (in seconds)
% 1.98/1.23  ----------------------
% 2.07/1.24  Preprocessing        : 0.30
% 2.07/1.24  Parsing              : 0.16
% 2.07/1.24  CNF conversion       : 0.02
% 2.07/1.24  Main loop            : 0.15
% 2.07/1.24  Inferencing          : 0.06
% 2.07/1.24  Reduction            : 0.04
% 2.07/1.24  Demodulation         : 0.03
% 2.07/1.24  BG Simplification    : 0.01
% 2.07/1.24  Subsumption          : 0.02
% 2.07/1.24  Abstraction          : 0.01
% 2.07/1.24  MUC search           : 0.00
% 2.07/1.24  Cooper               : 0.00
% 2.07/1.24  Total                : 0.48
% 2.07/1.24  Index Insertion      : 0.00
% 2.07/1.24  Index Deletion       : 0.00
% 2.07/1.24  Index Matching       : 0.00
% 2.07/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
