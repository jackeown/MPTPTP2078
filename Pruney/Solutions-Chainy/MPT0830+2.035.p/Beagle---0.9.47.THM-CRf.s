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
% DateTime   : Thu Dec  3 10:07:30 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   55 (  84 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 135 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_33,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_46,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_12,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(k7_relat_1(C_8,A_6))
      | ~ v4_relat_1(C_8,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    ! [A_6] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_6))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_12])).

tff(c_55,plain,(
    ! [A_6] : v1_relat_1(k7_relat_1('#skF_4',A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_52])).

tff(c_67,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(k7_relat_1(C_51,A_52),A_52)
      | ~ v4_relat_1(C_51,B_53)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ! [A_52] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_52),A_52)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_67])).

tff(c_75,plain,(
    ! [A_52] : v4_relat_1(k7_relat_1('#skF_4',A_52),A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_71])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_161,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( m1_subset_1(A_100,k1_zfmisc_1(k2_zfmisc_1(B_101,C_102)))
      | ~ r1_tarski(A_100,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(B_101,C_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_292,plain,(
    ! [B_122,A_123,B_124,C_125] :
      ( m1_subset_1(k7_relat_1(B_122,A_123),k1_zfmisc_1(k2_zfmisc_1(B_124,C_125)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(B_124,C_125)))
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_16,c_161])).

tff(c_24,plain,(
    ! [D_23,B_21,C_22,A_20] :
      ( m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(B_21,C_22)))
      | ~ r1_tarski(k1_relat_1(D_23),B_21)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_20,C_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_764,plain,(
    ! [A_195,C_194,B_196,B_197,B_198] :
      ( m1_subset_1(k7_relat_1(B_198,A_195),k1_zfmisc_1(k2_zfmisc_1(B_197,C_194)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_198,A_195)),B_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_zfmisc_1(B_196,C_194)))
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_292,c_24])).

tff(c_778,plain,(
    ! [A_195,B_197] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_195),k1_zfmisc_1(k2_zfmisc_1(B_197,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_195)),B_197)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_764])).

tff(c_790,plain,(
    ! [A_199,B_200] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_199),k1_zfmisc_1(k2_zfmisc_1(B_200,'#skF_3')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_199)),B_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_778])).

tff(c_135,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( k5_relset_1(A_83,B_84,C_85,D_86) = k7_relat_1(C_85,D_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,(
    ! [D_86] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_86) = k7_relat_1('#skF_4',D_86) ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_28,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_139,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_28])).

tff(c_836,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_790,c_139])).

tff(c_846,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_836])).

tff(c_850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_75,c_846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.42  
% 2.90/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.42  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.90/1.42  
% 2.90/1.42  %Foreground sorts:
% 2.90/1.42  
% 2.90/1.42  
% 2.90/1.42  %Background operators:
% 2.90/1.42  
% 2.90/1.42  
% 2.90/1.42  %Foreground operators:
% 2.90/1.42  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.90/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.90/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.90/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.42  
% 2.90/1.43  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.90/1.43  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.90/1.43  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.90/1.43  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.43  tff(f_48, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.90/1.43  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.90/1.43  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.90/1.43  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 2.90/1.43  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.90/1.43  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.90/1.43  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.90/1.43  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.90/1.43  tff(c_33, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.43  tff(c_36, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_33])).
% 2.90/1.43  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 2.90/1.43  tff(c_46, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.90/1.43  tff(c_50, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.90/1.43  tff(c_12, plain, (![C_8, A_6, B_7]: (v1_relat_1(k7_relat_1(C_8, A_6)) | ~v4_relat_1(C_8, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.43  tff(c_52, plain, (![A_6]: (v1_relat_1(k7_relat_1('#skF_4', A_6)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_12])).
% 2.90/1.43  tff(c_55, plain, (![A_6]: (v1_relat_1(k7_relat_1('#skF_4', A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_52])).
% 2.90/1.43  tff(c_67, plain, (![C_51, A_52, B_53]: (v4_relat_1(k7_relat_1(C_51, A_52), A_52) | ~v4_relat_1(C_51, B_53) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.43  tff(c_71, plain, (![A_52]: (v4_relat_1(k7_relat_1('#skF_4', A_52), A_52) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_67])).
% 2.90/1.43  tff(c_75, plain, (![A_52]: (v4_relat_1(k7_relat_1('#skF_4', A_52), A_52))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_71])).
% 2.90/1.43  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.43  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.90/1.43  tff(c_161, plain, (![A_100, B_101, C_102, D_103]: (m1_subset_1(A_100, k1_zfmisc_1(k2_zfmisc_1(B_101, C_102))) | ~r1_tarski(A_100, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(B_101, C_102))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.90/1.43  tff(c_292, plain, (![B_122, A_123, B_124, C_125]: (m1_subset_1(k7_relat_1(B_122, A_123), k1_zfmisc_1(k2_zfmisc_1(B_124, C_125))) | ~m1_subset_1(B_122, k1_zfmisc_1(k2_zfmisc_1(B_124, C_125))) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_16, c_161])).
% 2.90/1.43  tff(c_24, plain, (![D_23, B_21, C_22, A_20]: (m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(B_21, C_22))) | ~r1_tarski(k1_relat_1(D_23), B_21) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_20, C_22))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.43  tff(c_764, plain, (![A_195, C_194, B_196, B_197, B_198]: (m1_subset_1(k7_relat_1(B_198, A_195), k1_zfmisc_1(k2_zfmisc_1(B_197, C_194))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_198, A_195)), B_197) | ~m1_subset_1(B_198, k1_zfmisc_1(k2_zfmisc_1(B_196, C_194))) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_292, c_24])).
% 2.90/1.43  tff(c_778, plain, (![A_195, B_197]: (m1_subset_1(k7_relat_1('#skF_4', A_195), k1_zfmisc_1(k2_zfmisc_1(B_197, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_195)), B_197) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_764])).
% 2.90/1.43  tff(c_790, plain, (![A_199, B_200]: (m1_subset_1(k7_relat_1('#skF_4', A_199), k1_zfmisc_1(k2_zfmisc_1(B_200, '#skF_3'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_199)), B_200))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_778])).
% 2.90/1.43  tff(c_135, plain, (![A_83, B_84, C_85, D_86]: (k5_relset_1(A_83, B_84, C_85, D_86)=k7_relat_1(C_85, D_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.90/1.43  tff(c_138, plain, (![D_86]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_86)=k7_relat_1('#skF_4', D_86))), inference(resolution, [status(thm)], [c_30, c_135])).
% 2.90/1.43  tff(c_28, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.90/1.43  tff(c_139, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_28])).
% 2.90/1.43  tff(c_836, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_790, c_139])).
% 2.90/1.43  tff(c_846, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_836])).
% 2.90/1.43  tff(c_850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_75, c_846])).
% 2.90/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.43  
% 2.90/1.43  Inference rules
% 2.90/1.43  ----------------------
% 2.90/1.43  #Ref     : 0
% 2.90/1.43  #Sup     : 181
% 2.90/1.43  #Fact    : 0
% 2.90/1.43  #Define  : 0
% 2.90/1.43  #Split   : 0
% 2.90/1.43  #Chain   : 0
% 2.90/1.43  #Close   : 0
% 2.90/1.43  
% 2.90/1.43  Ordering : KBO
% 2.90/1.43  
% 2.90/1.43  Simplification rules
% 2.90/1.43  ----------------------
% 2.90/1.43  #Subsume      : 12
% 2.90/1.43  #Demod        : 120
% 2.90/1.43  #Tautology    : 41
% 2.90/1.43  #SimpNegUnit  : 0
% 2.90/1.43  #BackRed      : 1
% 2.90/1.43  
% 2.90/1.43  #Partial instantiations: 0
% 2.90/1.43  #Strategies tried      : 1
% 2.90/1.43  
% 2.90/1.43  Timing (in seconds)
% 2.90/1.43  ----------------------
% 2.90/1.44  Preprocessing        : 0.29
% 2.90/1.44  Parsing              : 0.16
% 2.90/1.44  CNF conversion       : 0.02
% 2.90/1.44  Main loop            : 0.39
% 2.90/1.44  Inferencing          : 0.14
% 2.90/1.44  Reduction            : 0.13
% 2.90/1.44  Demodulation         : 0.10
% 2.90/1.44  BG Simplification    : 0.02
% 2.90/1.44  Subsumption          : 0.07
% 2.90/1.44  Abstraction          : 0.02
% 2.90/1.44  MUC search           : 0.00
% 2.90/1.44  Cooper               : 0.00
% 2.90/1.44  Total                : 0.71
% 2.90/1.44  Index Insertion      : 0.00
% 2.90/1.44  Index Deletion       : 0.00
% 2.90/1.44  Index Matching       : 0.00
% 2.90/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
