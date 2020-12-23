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
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 112 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k5_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_73,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k5_relset_1(A_38,B_39,C_40,D_41) = k7_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [D_41] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_41) = k7_relat_1('#skF_4',D_41) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_18,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_18])).

tff(c_20,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_24])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_27])).

tff(c_96,plain,(
    ! [D_46] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_46) = k7_relat_1('#skF_4',D_46) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( m1_subset_1(k5_relset_1(A_14,B_15,C_16,D_17),k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    ! [D_46] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_46),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_14])).

tff(c_110,plain,(
    ! [D_47] : m1_subset_1(k7_relat_1('#skF_4',D_47),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_102])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [D_47] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_47))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_129,plain,(
    ! [D_47] : v1_relat_1(k7_relat_1('#skF_4',D_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [D_50] : v4_relat_1(k7_relat_1('#skF_4',D_50),'#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_12])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_142,plain,(
    ! [D_50] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_50),'#skF_3') = k7_relat_1('#skF_4',D_50)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_50)) ) ),
    inference(resolution,[status(thm)],[c_139,c_8])).

tff(c_149,plain,(
    ! [D_51] : k7_relat_1(k7_relat_1('#skF_4',D_51),'#skF_3') = k7_relat_1('#skF_4',D_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_142])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( k7_relat_1(k7_relat_1(C_8,A_6),B_7) = k1_xboole_0
      | ~ r1_xboole_0(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_158,plain,(
    ! [D_51] :
      ( k7_relat_1('#skF_4',D_51) = k1_xboole_0
      | ~ r1_xboole_0(D_51,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_6])).

tff(c_178,plain,(
    ! [D_52] :
      ( k7_relat_1('#skF_4',D_52) = k1_xboole_0
      | ~ r1_xboole_0(D_52,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_158])).

tff(c_181,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_178])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.87/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.87/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.17  
% 1.87/1.18  tff(f_67, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 1.87/1.18  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.87/1.18  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.87/1.18  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.87/1.18  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k5_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relset_1)).
% 1.87/1.18  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.87/1.18  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.87/1.18  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.87/1.18  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.18  tff(c_73, plain, (![A_38, B_39, C_40, D_41]: (k5_relset_1(A_38, B_39, C_40, D_41)=k7_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.18  tff(c_76, plain, (![D_41]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_41)=k7_relat_1('#skF_4', D_41))), inference(resolution, [status(thm)], [c_22, c_73])).
% 1.87/1.18  tff(c_18, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.18  tff(c_95, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_76, c_18])).
% 1.87/1.18  tff(c_20, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.18  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.18  tff(c_24, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.18  tff(c_27, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_24])).
% 1.87/1.18  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_27])).
% 1.87/1.18  tff(c_96, plain, (![D_46]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_46)=k7_relat_1('#skF_4', D_46))), inference(resolution, [status(thm)], [c_22, c_73])).
% 1.87/1.18  tff(c_14, plain, (![A_14, B_15, C_16, D_17]: (m1_subset_1(k5_relset_1(A_14, B_15, C_16, D_17), k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.18  tff(c_102, plain, (![D_46]: (m1_subset_1(k7_relat_1('#skF_4', D_46), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_96, c_14])).
% 1.87/1.18  tff(c_110, plain, (![D_47]: (m1_subset_1(k7_relat_1('#skF_4', D_47), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_102])).
% 1.87/1.18  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.18  tff(c_121, plain, (![D_47]: (v1_relat_1(k7_relat_1('#skF_4', D_47)) | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_110, c_2])).
% 1.87/1.18  tff(c_129, plain, (![D_47]: (v1_relat_1(k7_relat_1('#skF_4', D_47)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 1.87/1.18  tff(c_12, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.18  tff(c_139, plain, (![D_50]: (v4_relat_1(k7_relat_1('#skF_4', D_50), '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_12])).
% 1.87/1.18  tff(c_8, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.18  tff(c_142, plain, (![D_50]: (k7_relat_1(k7_relat_1('#skF_4', D_50), '#skF_3')=k7_relat_1('#skF_4', D_50) | ~v1_relat_1(k7_relat_1('#skF_4', D_50)))), inference(resolution, [status(thm)], [c_139, c_8])).
% 1.87/1.18  tff(c_149, plain, (![D_51]: (k7_relat_1(k7_relat_1('#skF_4', D_51), '#skF_3')=k7_relat_1('#skF_4', D_51))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_142])).
% 1.87/1.18  tff(c_6, plain, (![C_8, A_6, B_7]: (k7_relat_1(k7_relat_1(C_8, A_6), B_7)=k1_xboole_0 | ~r1_xboole_0(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.87/1.18  tff(c_158, plain, (![D_51]: (k7_relat_1('#skF_4', D_51)=k1_xboole_0 | ~r1_xboole_0(D_51, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_6])).
% 1.87/1.18  tff(c_178, plain, (![D_52]: (k7_relat_1('#skF_4', D_52)=k1_xboole_0 | ~r1_xboole_0(D_52, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_158])).
% 1.87/1.18  tff(c_181, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_178])).
% 1.87/1.18  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_181])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 35
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 0
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 0
% 1.87/1.18  #Demod        : 17
% 1.87/1.18  #Tautology    : 13
% 1.87/1.18  #SimpNegUnit  : 1
% 1.87/1.18  #BackRed      : 1
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.28
% 1.87/1.18  Parsing              : 0.15
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.14
% 1.87/1.18  Inferencing          : 0.06
% 1.87/1.18  Reduction            : 0.04
% 1.87/1.18  Demodulation         : 0.03
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.45
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
