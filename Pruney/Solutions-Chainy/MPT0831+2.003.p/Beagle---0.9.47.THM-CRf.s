%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:32 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 103 expanded)
%              Number of equality atoms :   11 (  11 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_96,plain,(
    ! [A_48,B_49,D_50] :
      ( r2_relset_1(A_48,B_49,D_50,D_50)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_96])).

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

tff(c_75,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k1_relat_1(B_44),A_45)
      | ~ v4_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [B_46,A_47] :
      ( k2_xboole_0(k1_relat_1(B_46),A_47) = A_47
      | ~ v4_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [B_51,C_52,A_53] :
      ( r1_tarski(k1_relat_1(B_51),C_52)
      | ~ r1_tarski(A_53,C_52)
      | ~ v4_relat_1(B_51,A_53)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2])).

tff(c_110,plain,(
    ! [B_54] :
      ( r1_tarski(k1_relat_1(B_54),'#skF_3')
      | ~ v4_relat_1(B_54,'#skF_2')
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( v4_relat_1(B_7,A_6)
      | ~ r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [B_55] :
      ( v4_relat_1(B_55,'#skF_3')
      | ~ v4_relat_1(B_55,'#skF_2')
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_110,c_6])).

tff(c_125,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_122])).

tff(c_128,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_125])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_10])).

tff(c_134,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_131])).

tff(c_135,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k5_relset_1(A_56,B_57,C_58,D_59) = k7_relat_1(C_58,D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    ! [D_59] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_59) = k7_relat_1('#skF_4',D_59) ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_24])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_134,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.25  
% 1.93/1.25  %Foreground sorts:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Background operators:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Foreground operators:
% 1.93/1.25  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.25  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.93/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.93/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.93/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.93/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.25  
% 1.93/1.27  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 1.93/1.27  tff(f_67, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.93/1.27  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.93/1.27  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.93/1.27  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.93/1.27  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.93/1.27  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.93/1.27  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.93/1.27  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.93/1.27  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.27  tff(c_96, plain, (![A_48, B_49, D_50]: (r2_relset_1(A_48, B_49, D_50, D_50) | ~m1_subset_1(D_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.93/1.27  tff(c_99, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_96])).
% 1.93/1.27  tff(c_38, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.27  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_38])).
% 1.93/1.27  tff(c_59, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.27  tff(c_63, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_59])).
% 1.93/1.27  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.27  tff(c_75, plain, (![B_44, A_45]: (r1_tarski(k1_relat_1(B_44), A_45) | ~v4_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.27  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.27  tff(c_84, plain, (![B_46, A_47]: (k2_xboole_0(k1_relat_1(B_46), A_47)=A_47 | ~v4_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_75, c_4])).
% 1.93/1.27  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.27  tff(c_100, plain, (![B_51, C_52, A_53]: (r1_tarski(k1_relat_1(B_51), C_52) | ~r1_tarski(A_53, C_52) | ~v4_relat_1(B_51, A_53) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_84, c_2])).
% 1.93/1.27  tff(c_110, plain, (![B_54]: (r1_tarski(k1_relat_1(B_54), '#skF_3') | ~v4_relat_1(B_54, '#skF_2') | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_26, c_100])).
% 1.93/1.27  tff(c_6, plain, (![B_7, A_6]: (v4_relat_1(B_7, A_6) | ~r1_tarski(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.27  tff(c_122, plain, (![B_55]: (v4_relat_1(B_55, '#skF_3') | ~v4_relat_1(B_55, '#skF_2') | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_110, c_6])).
% 1.93/1.27  tff(c_125, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_122])).
% 1.93/1.27  tff(c_128, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_125])).
% 1.93/1.27  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.27  tff(c_131, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_10])).
% 1.93/1.27  tff(c_134, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_131])).
% 1.93/1.27  tff(c_135, plain, (![A_56, B_57, C_58, D_59]: (k5_relset_1(A_56, B_57, C_58, D_59)=k7_relat_1(C_58, D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.27  tff(c_138, plain, (![D_59]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_59)=k7_relat_1('#skF_4', D_59))), inference(resolution, [status(thm)], [c_28, c_135])).
% 1.93/1.27  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.27  tff(c_143, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_24])).
% 1.93/1.27  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_134, c_143])).
% 1.93/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.27  
% 1.93/1.27  Inference rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Ref     : 0
% 1.93/1.27  #Sup     : 28
% 1.93/1.27  #Fact    : 0
% 1.93/1.27  #Define  : 0
% 1.93/1.27  #Split   : 0
% 1.93/1.27  #Chain   : 0
% 1.93/1.27  #Close   : 0
% 1.93/1.27  
% 1.93/1.27  Ordering : KBO
% 1.93/1.27  
% 1.93/1.27  Simplification rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Subsume      : 0
% 1.93/1.27  #Demod        : 6
% 1.93/1.27  #Tautology    : 9
% 1.93/1.27  #SimpNegUnit  : 0
% 1.93/1.27  #BackRed      : 1
% 1.93/1.27  
% 1.93/1.27  #Partial instantiations: 0
% 1.93/1.27  #Strategies tried      : 1
% 1.93/1.27  
% 1.93/1.27  Timing (in seconds)
% 1.93/1.27  ----------------------
% 1.93/1.27  Preprocessing        : 0.29
% 1.93/1.27  Parsing              : 0.15
% 1.93/1.27  CNF conversion       : 0.02
% 1.93/1.27  Main loop            : 0.14
% 1.93/1.27  Inferencing          : 0.06
% 1.93/1.27  Reduction            : 0.04
% 1.93/1.27  Demodulation         : 0.03
% 1.93/1.27  BG Simplification    : 0.01
% 1.93/1.27  Subsumption          : 0.02
% 1.93/1.27  Abstraction          : 0.01
% 1.93/1.27  MUC search           : 0.00
% 1.93/1.27  Cooper               : 0.00
% 1.93/1.27  Total                : 0.47
% 1.93/1.27  Index Insertion      : 0.00
% 1.93/1.27  Index Deletion       : 0.00
% 1.93/1.27  Index Matching       : 0.00
% 1.93/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
