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
% DateTime   : Thu Dec  3 10:07:37 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 117 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_118,plain,(
    ! [A_49,B_50,D_51] :
      ( r2_relset_1(A_49,B_50,D_51,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_118])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_60,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_60])).

tff(c_42,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(k1_relat_1(B_32),A_33)
      | ~ v4_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_37,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,C_29)
      | ~ r1_tarski(B_30,C_29)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_3')
      | ~ r1_tarski(A_28,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_49,plain,(
    ! [B_32] :
      ( r1_tarski(k1_relat_1(B_32),'#skF_3')
      | ~ v4_relat_1(B_32,'#skF_2')
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_42,c_40])).

tff(c_65,plain,(
    ! [B_41,A_42] :
      ( v4_relat_1(B_41,A_42)
      | ~ r1_tarski(k1_relat_1(B_41),A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,(
    ! [B_45] :
      ( v4_relat_1(B_45,'#skF_3')
      | ~ v4_relat_1(B_45,'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_49,c_65])).

tff(c_86,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_83])).

tff(c_89,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_86])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ r1_tarski(k1_relat_1(B_43),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,(
    ! [B_46,A_47] :
      ( k7_relat_1(B_46,A_47) = B_46
      | ~ v4_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_93,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_89,c_90])).

tff(c_99,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93])).

tff(c_127,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k5_relset_1(A_55,B_56,C_57,D_58) = k7_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [D_58] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_58) = k7_relat_1('#skF_4',D_58) ),
    inference(resolution,[status(thm)],[c_28,c_127])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_24])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_99,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.72/1.16  
% 1.72/1.16  %Foreground sorts:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Background operators:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Foreground operators:
% 1.72/1.16  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 1.72/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.72/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.72/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.72/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.72/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.16  
% 1.72/1.17  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 1.72/1.17  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.72/1.17  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.72/1.17  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.72/1.17  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.72/1.17  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 1.72/1.17  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.72/1.17  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.72/1.17  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 1.72/1.17  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.72/1.17  tff(c_118, plain, (![A_49, B_50, D_51]: (r2_relset_1(A_49, B_50, D_51, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.72/1.17  tff(c_121, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_118])).
% 1.72/1.17  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.72/1.17  tff(c_30, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.17  tff(c_33, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_30])).
% 1.72/1.17  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_33])).
% 1.72/1.17  tff(c_60, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.72/1.17  tff(c_64, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_60])).
% 1.72/1.17  tff(c_42, plain, (![B_32, A_33]: (r1_tarski(k1_relat_1(B_32), A_33) | ~v4_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.72/1.17  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.72/1.17  tff(c_37, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, C_29) | ~r1_tarski(B_30, C_29) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.17  tff(c_40, plain, (![A_28]: (r1_tarski(A_28, '#skF_3') | ~r1_tarski(A_28, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_37])).
% 1.72/1.17  tff(c_49, plain, (![B_32]: (r1_tarski(k1_relat_1(B_32), '#skF_3') | ~v4_relat_1(B_32, '#skF_2') | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_42, c_40])).
% 1.72/1.17  tff(c_65, plain, (![B_41, A_42]: (v4_relat_1(B_41, A_42) | ~r1_tarski(k1_relat_1(B_41), A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.72/1.17  tff(c_83, plain, (![B_45]: (v4_relat_1(B_45, '#skF_3') | ~v4_relat_1(B_45, '#skF_2') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_49, c_65])).
% 1.72/1.17  tff(c_86, plain, (v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_83])).
% 1.72/1.17  tff(c_89, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_86])).
% 1.72/1.17  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.72/1.17  tff(c_74, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~r1_tarski(k1_relat_1(B_43), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.72/1.17  tff(c_90, plain, (![B_46, A_47]: (k7_relat_1(B_46, A_47)=B_46 | ~v4_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_8, c_74])).
% 1.72/1.17  tff(c_93, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_89, c_90])).
% 1.72/1.17  tff(c_99, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 1.72/1.17  tff(c_127, plain, (![A_55, B_56, C_57, D_58]: (k5_relset_1(A_55, B_56, C_57, D_58)=k7_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.72/1.17  tff(c_130, plain, (![D_58]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_58)=k7_relat_1('#skF_4', D_58))), inference(resolution, [status(thm)], [c_28, c_127])).
% 1.72/1.17  tff(c_24, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.72/1.17  tff(c_131, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_24])).
% 1.72/1.17  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_99, c_131])).
% 1.72/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  Inference rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Ref     : 0
% 1.72/1.17  #Sup     : 22
% 1.72/1.17  #Fact    : 0
% 1.72/1.17  #Define  : 0
% 1.72/1.17  #Split   : 0
% 1.72/1.17  #Chain   : 0
% 1.72/1.17  #Close   : 0
% 1.72/1.17  
% 1.72/1.17  Ordering : KBO
% 1.72/1.17  
% 1.72/1.17  Simplification rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Subsume      : 0
% 1.72/1.17  #Demod        : 9
% 1.72/1.17  #Tautology    : 6
% 1.72/1.17  #SimpNegUnit  : 0
% 1.72/1.17  #BackRed      : 1
% 1.72/1.17  
% 1.72/1.17  #Partial instantiations: 0
% 1.72/1.17  #Strategies tried      : 1
% 1.72/1.17  
% 1.72/1.17  Timing (in seconds)
% 1.72/1.17  ----------------------
% 1.72/1.18  Preprocessing        : 0.29
% 1.72/1.18  Parsing              : 0.16
% 1.72/1.18  CNF conversion       : 0.02
% 1.72/1.18  Main loop            : 0.13
% 1.72/1.18  Inferencing          : 0.05
% 1.72/1.18  Reduction            : 0.04
% 1.72/1.18  Demodulation         : 0.03
% 1.72/1.18  BG Simplification    : 0.01
% 1.72/1.18  Subsumption          : 0.02
% 1.72/1.18  Abstraction          : 0.01
% 1.72/1.18  MUC search           : 0.00
% 1.72/1.18  Cooper               : 0.00
% 1.72/1.18  Total                : 0.45
% 1.72/1.18  Index Insertion      : 0.00
% 1.72/1.18  Index Deletion       : 0.00
% 1.72/1.18  Index Matching       : 0.00
% 1.72/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
