%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  85 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_20,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_24])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_35])).

tff(c_44,plain,(
    ! [C_29,A_30,B_31] :
      ( v4_relat_1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_49,plain,(
    ! [B_32,A_33] :
      ( k7_relat_1(B_32,A_33) = B_32
      | ~ v4_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_49])).

tff(c_55,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_60,plain,(
    ! [C_34,A_35,B_36] :
      ( k7_relat_1(k7_relat_1(C_34,A_35),B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [B_36] :
      ( k7_relat_1('#skF_4',B_36) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_36)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_60])).

tff(c_84,plain,(
    ! [B_41] :
      ( k7_relat_1('#skF_4',B_41) = k1_xboole_0
      | ~ r1_xboole_0('#skF_3',B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_75])).

tff(c_88,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27,c_84])).

tff(c_80,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( k5_relset_1(A_37,B_38,C_39,D_40) = k7_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_83,plain,(
    ! [D_40] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_40) = k7_relat_1('#skF_4',D_40) ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_18,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_18])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.58  
% 2.29/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.59  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.29/1.59  
% 2.29/1.59  %Foreground sorts:
% 2.29/1.59  
% 2.29/1.59  
% 2.29/1.59  %Background operators:
% 2.29/1.59  
% 2.29/1.59  
% 2.29/1.59  %Foreground operators:
% 2.29/1.59  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.29/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.29/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.29/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.59  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.29/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.29/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.59  
% 2.29/1.61  tff(f_67, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.29/1.61  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.29/1.61  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.29/1.61  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.29/1.61  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.29/1.61  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.29/1.61  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 2.29/1.61  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.29/1.61  tff(c_20, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.61  tff(c_24, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.61  tff(c_27, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_24])).
% 2.29/1.61  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.29/1.61  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.61  tff(c_32, plain, (![B_24, A_25]: (v1_relat_1(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_25)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.29/1.61  tff(c_35, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_32])).
% 2.29/1.61  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_35])).
% 2.29/1.61  tff(c_44, plain, (![C_29, A_30, B_31]: (v4_relat_1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.29/1.61  tff(c_48, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_44])).
% 2.29/1.61  tff(c_49, plain, (![B_32, A_33]: (k7_relat_1(B_32, A_33)=B_32 | ~v4_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.61  tff(c_52, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_49])).
% 2.29/1.61  tff(c_55, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.29/1.61  tff(c_60, plain, (![C_34, A_35, B_36]: (k7_relat_1(k7_relat_1(C_34, A_35), B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.61  tff(c_75, plain, (![B_36]: (k7_relat_1('#skF_4', B_36)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_36) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_60])).
% 2.29/1.61  tff(c_84, plain, (![B_41]: (k7_relat_1('#skF_4', B_41)=k1_xboole_0 | ~r1_xboole_0('#skF_3', B_41))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_75])).
% 2.29/1.61  tff(c_88, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_27, c_84])).
% 2.29/1.61  tff(c_80, plain, (![A_37, B_38, C_39, D_40]: (k5_relset_1(A_37, B_38, C_39, D_40)=k7_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.61  tff(c_83, plain, (![D_40]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_40)=k7_relat_1('#skF_4', D_40))), inference(resolution, [status(thm)], [c_22, c_80])).
% 2.29/1.61  tff(c_18, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.61  tff(c_110, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_83, c_18])).
% 2.29/1.61  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_110])).
% 2.29/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.61  
% 2.29/1.61  Inference rules
% 2.29/1.61  ----------------------
% 2.29/1.61  #Ref     : 0
% 2.29/1.61  #Sup     : 22
% 2.29/1.61  #Fact    : 0
% 2.29/1.61  #Define  : 0
% 2.29/1.61  #Split   : 0
% 2.29/1.61  #Chain   : 0
% 2.29/1.61  #Close   : 0
% 2.29/1.61  
% 2.29/1.61  Ordering : KBO
% 2.29/1.61  
% 2.29/1.61  Simplification rules
% 2.29/1.61  ----------------------
% 2.29/1.61  #Subsume      : 0
% 2.29/1.61  #Demod        : 7
% 2.29/1.61  #Tautology    : 9
% 2.29/1.61  #SimpNegUnit  : 0
% 2.29/1.61  #BackRed      : 1
% 2.29/1.61  
% 2.29/1.61  #Partial instantiations: 0
% 2.29/1.61  #Strategies tried      : 1
% 2.29/1.61  
% 2.29/1.61  Timing (in seconds)
% 2.29/1.61  ----------------------
% 2.29/1.61  Preprocessing        : 0.46
% 2.29/1.61  Parsing              : 0.24
% 2.29/1.61  CNF conversion       : 0.03
% 2.29/1.61  Main loop            : 0.20
% 2.29/1.61  Inferencing          : 0.08
% 2.29/1.61  Reduction            : 0.06
% 2.29/1.61  Demodulation         : 0.05
% 2.29/1.61  BG Simplification    : 0.02
% 2.29/1.61  Subsumption          : 0.03
% 2.29/1.61  Abstraction          : 0.01
% 2.29/1.61  MUC search           : 0.00
% 2.29/1.61  Cooper               : 0.00
% 2.29/1.61  Total                : 0.71
% 2.29/1.61  Index Insertion      : 0.00
% 2.29/1.61  Index Deletion       : 0.00
% 2.29/1.61  Index Matching       : 0.00
% 2.29/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
