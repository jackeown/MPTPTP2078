%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:31 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 128 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 213 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_32,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_29,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_41,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_12,plain,(
    ! [C_12,A_10,B_11] :
      ( v5_relat_1(k7_relat_1(C_12,A_10),B_11)
      | ~ v5_relat_1(C_12,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(k7_relat_1(C_37,A_38))
      | ~ v5_relat_1(C_37,B_39)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    ! [A_38] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_38))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_45,c_47])).

tff(c_52,plain,(
    ! [A_38] : v1_relat_1(k7_relat_1('#skF_4',A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_49])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    ! [C_57,A_58,B_59] :
      ( m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ r1_tarski(k2_relat_1(C_57),B_59)
      | ~ r1_tarski(k1_relat_1(C_57),A_58)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( k5_relset_1(A_46,B_47,C_48,D_49) = k7_relat_1(C_48,D_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ! [D_49] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_49) = k7_relat_1('#skF_4',D_49) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_67,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24])).

tff(c_90,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_87,c_67])).

tff(c_104,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_90])).

tff(c_111,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_114,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_111])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_114])).

tff(c_119,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_123,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_126,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_123])).

tff(c_129,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_45,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.18  
% 2.05/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.18  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.18  
% 2.05/1.18  %Foreground sorts:
% 2.05/1.18  
% 2.05/1.18  
% 2.05/1.18  %Background operators:
% 2.05/1.18  
% 2.05/1.18  
% 2.05/1.18  %Foreground operators:
% 2.05/1.18  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.05/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.05/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.18  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.18  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.05/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.18  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.05/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.18  
% 2.05/1.20  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.05/1.20  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.05/1.20  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.05/1.20  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.05/1.20  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc22_relat_1)).
% 2.05/1.20  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.05/1.20  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.05/1.20  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.05/1.20  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.05/1.20  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.20  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.20  tff(c_29, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.20  tff(c_32, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.05/1.20  tff(c_35, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 2.05/1.20  tff(c_41, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.20  tff(c_45, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_41])).
% 2.05/1.20  tff(c_12, plain, (![C_12, A_10, B_11]: (v5_relat_1(k7_relat_1(C_12, A_10), B_11) | ~v5_relat_1(C_12, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.20  tff(c_47, plain, (![C_37, A_38, B_39]: (v1_relat_1(k7_relat_1(C_37, A_38)) | ~v5_relat_1(C_37, B_39) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.05/1.20  tff(c_49, plain, (![A_38]: (v1_relat_1(k7_relat_1('#skF_4', A_38)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_45, c_47])).
% 2.05/1.20  tff(c_52, plain, (![A_38]: (v1_relat_1(k7_relat_1('#skF_4', A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_49])).
% 2.05/1.20  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.20  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.05/1.20  tff(c_87, plain, (![C_57, A_58, B_59]: (m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~r1_tarski(k2_relat_1(C_57), B_59) | ~r1_tarski(k1_relat_1(C_57), A_58) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.05/1.20  tff(c_63, plain, (![A_46, B_47, C_48, D_49]: (k5_relset_1(A_46, B_47, C_48, D_49)=k7_relat_1(C_48, D_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.05/1.20  tff(c_66, plain, (![D_49]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_49)=k7_relat_1('#skF_4', D_49))), inference(resolution, [status(thm)], [c_26, c_63])).
% 2.05/1.20  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.20  tff(c_67, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_24])).
% 2.05/1.20  tff(c_90, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_87, c_67])).
% 2.05/1.20  tff(c_104, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_90])).
% 2.05/1.20  tff(c_111, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_104])).
% 2.05/1.20  tff(c_114, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_111])).
% 2.05/1.20  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_114])).
% 2.05/1.20  tff(c_119, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_104])).
% 2.05/1.20  tff(c_123, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_119])).
% 2.05/1.20  tff(c_126, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_123])).
% 2.05/1.20  tff(c_129, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_126])).
% 2.05/1.20  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_45, c_129])).
% 2.05/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.20  
% 2.05/1.20  Inference rules
% 2.05/1.20  ----------------------
% 2.05/1.20  #Ref     : 0
% 2.05/1.20  #Sup     : 19
% 2.05/1.20  #Fact    : 0
% 2.05/1.20  #Define  : 0
% 2.05/1.20  #Split   : 1
% 2.05/1.20  #Chain   : 0
% 2.05/1.20  #Close   : 0
% 2.05/1.20  
% 2.05/1.20  Ordering : KBO
% 2.05/1.20  
% 2.05/1.20  Simplification rules
% 2.05/1.20  ----------------------
% 2.05/1.20  #Subsume      : 1
% 2.05/1.20  #Demod        : 11
% 2.05/1.20  #Tautology    : 4
% 2.05/1.20  #SimpNegUnit  : 0
% 2.05/1.20  #BackRed      : 1
% 2.05/1.20  
% 2.05/1.20  #Partial instantiations: 0
% 2.05/1.20  #Strategies tried      : 1
% 2.05/1.20  
% 2.05/1.20  Timing (in seconds)
% 2.05/1.20  ----------------------
% 2.05/1.20  Preprocessing        : 0.29
% 2.05/1.20  Parsing              : 0.15
% 2.05/1.20  CNF conversion       : 0.02
% 2.05/1.20  Main loop            : 0.14
% 2.05/1.20  Inferencing          : 0.05
% 2.05/1.20  Reduction            : 0.04
% 2.05/1.20  Demodulation         : 0.03
% 2.05/1.20  BG Simplification    : 0.01
% 2.05/1.20  Subsumption          : 0.02
% 2.05/1.20  Abstraction          : 0.01
% 2.05/1.20  MUC search           : 0.00
% 2.05/1.20  Cooper               : 0.00
% 2.05/1.20  Total                : 0.46
% 2.05/1.20  Index Insertion      : 0.00
% 2.05/1.20  Index Deletion       : 0.00
% 2.05/1.20  Index Matching       : 0.00
% 2.05/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
