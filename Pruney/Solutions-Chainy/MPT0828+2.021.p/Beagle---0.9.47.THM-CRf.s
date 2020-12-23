%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:20 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 130 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 229 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_176,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_180,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_176])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_67,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_181,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_67])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_62,plain,(
    ! [C_31,A_32,B_33] :
      ( v4_relat_1(C_31,A_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_186,plain,(
    ! [C_60,A_61,B_62,D_63] :
      ( r1_tarski(C_60,k1_relset_1(A_61,B_62,D_63))
      | ~ r1_tarski(k6_relat_1(C_60),D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_195,plain,(
    ! [A_66,B_67] :
      ( r1_tarski('#skF_2',k1_relset_1(A_66,B_67,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_198,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_195])).

tff(c_200,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_198])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [B_47,A_48] :
      ( k5_relat_1(B_47,k6_relat_1(A_48)) = B_47
      | ~ r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,(
    ! [A_9,A_48] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_48)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_48)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_142,plain,(
    ! [A_53,A_54] :
      ( k5_relat_1(k6_relat_1(A_53),k6_relat_1(A_54)) = k6_relat_1(A_53)
      | ~ r1_tarski(A_53,A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_95,plain,(
    ! [A_45,B_46] :
      ( k5_relat_1(k6_relat_1(A_45),B_46) = B_46
      | ~ r1_tarski(k1_relat_1(B_46),A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_101,plain,(
    ! [A_45,A_9] :
      ( k5_relat_1(k6_relat_1(A_45),k6_relat_1(A_9)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_45)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_95])).

tff(c_104,plain,(
    ! [A_45,A_9] :
      ( k5_relat_1(k6_relat_1(A_45),k6_relat_1(A_9)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_101])).

tff(c_148,plain,(
    ! [A_54,A_53] :
      ( k6_relat_1(A_54) = k6_relat_1(A_53)
      | ~ r1_tarski(A_54,A_53)
      | ~ r1_tarski(A_53,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_104])).

tff(c_203,plain,
    ( k6_relat_1(k1_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_200,c_148])).

tff(c_208,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_211,plain,
    ( ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_66,c_211])).

tff(c_216,plain,(
    k6_relat_1(k1_relat_1('#skF_3')) = k6_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_271,plain,(
    k1_relat_1(k6_relat_1('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_12])).

tff(c_282,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_271])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_282])).

tff(c_285,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_477,plain,(
    ! [C_111,A_112,B_113,D_114] :
      ( r1_tarski(C_111,k2_relset_1(A_112,B_113,D_114))
      | ~ r1_tarski(k6_relat_1(C_111),D_114)
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_481,plain,(
    ! [A_115,B_116] :
      ( r1_tarski('#skF_2',k2_relset_1(A_115,B_116,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(resolution,[status(thm)],[c_32,c_477])).

tff(c_484,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_481])).

tff(c_488,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.28/1.32  
% 2.28/1.32  %Foreground sorts:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Background operators:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Foreground operators:
% 2.28/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.28/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.32  
% 2.52/1.34  tff(f_85, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relset_1)).
% 2.52/1.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.52/1.34  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.52/1.34  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.52/1.34  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.52/1.34  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.52/1.34  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.52/1.34  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.52/1.34  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.52/1.34  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.52/1.34  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.52/1.34  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.52/1.34  tff(c_176, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.52/1.34  tff(c_180, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_176])).
% 2.52/1.34  tff(c_30, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.52/1.34  tff(c_67, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.52/1.34  tff(c_181, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_67])).
% 2.52/1.34  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.52/1.34  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.34  tff(c_55, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.52/1.34  tff(c_58, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_55])).
% 2.52/1.34  tff(c_61, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_58])).
% 2.52/1.34  tff(c_62, plain, (![C_31, A_32, B_33]: (v4_relat_1(C_31, A_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.34  tff(c_66, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.52/1.34  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.52/1.34  tff(c_32, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.52/1.34  tff(c_186, plain, (![C_60, A_61, B_62, D_63]: (r1_tarski(C_60, k1_relset_1(A_61, B_62, D_63)) | ~r1_tarski(k6_relat_1(C_60), D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.34  tff(c_195, plain, (![A_66, B_67]: (r1_tarski('#skF_2', k1_relset_1(A_66, B_67, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(resolution, [status(thm)], [c_32, c_186])).
% 2.52/1.34  tff(c_198, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_195])).
% 2.52/1.34  tff(c_200, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_198])).
% 2.52/1.34  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.34  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.52/1.34  tff(c_105, plain, (![B_47, A_48]: (k5_relat_1(B_47, k6_relat_1(A_48))=B_47 | ~r1_tarski(k2_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.52/1.34  tff(c_108, plain, (![A_9, A_48]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_48))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_48) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_105])).
% 2.52/1.34  tff(c_142, plain, (![A_53, A_54]: (k5_relat_1(k6_relat_1(A_53), k6_relat_1(A_54))=k6_relat_1(A_53) | ~r1_tarski(A_53, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_108])).
% 2.52/1.34  tff(c_95, plain, (![A_45, B_46]: (k5_relat_1(k6_relat_1(A_45), B_46)=B_46 | ~r1_tarski(k1_relat_1(B_46), A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.34  tff(c_101, plain, (![A_45, A_9]: (k5_relat_1(k6_relat_1(A_45), k6_relat_1(A_9))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_45) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_95])).
% 2.52/1.34  tff(c_104, plain, (![A_45, A_9]: (k5_relat_1(k6_relat_1(A_45), k6_relat_1(A_9))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_101])).
% 2.52/1.34  tff(c_148, plain, (![A_54, A_53]: (k6_relat_1(A_54)=k6_relat_1(A_53) | ~r1_tarski(A_54, A_53) | ~r1_tarski(A_53, A_54))), inference(superposition, [status(thm), theory('equality')], [c_142, c_104])).
% 2.52/1.34  tff(c_203, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_200, c_148])).
% 2.52/1.34  tff(c_208, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_203])).
% 2.52/1.34  tff(c_211, plain, (~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_208])).
% 2.52/1.34  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_66, c_211])).
% 2.52/1.34  tff(c_216, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k6_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_203])).
% 2.52/1.34  tff(c_271, plain, (k1_relat_1(k6_relat_1('#skF_2'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_12])).
% 2.52/1.34  tff(c_282, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_271])).
% 2.52/1.34  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_282])).
% 2.52/1.34  tff(c_285, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_30])).
% 2.52/1.34  tff(c_477, plain, (![C_111, A_112, B_113, D_114]: (r1_tarski(C_111, k2_relset_1(A_112, B_113, D_114)) | ~r1_tarski(k6_relat_1(C_111), D_114) | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.34  tff(c_481, plain, (![A_115, B_116]: (r1_tarski('#skF_2', k2_relset_1(A_115, B_116, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(resolution, [status(thm)], [c_32, c_477])).
% 2.52/1.34  tff(c_484, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_481])).
% 2.52/1.34  tff(c_488, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_484])).
% 2.52/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  Inference rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Ref     : 0
% 2.52/1.34  #Sup     : 98
% 2.52/1.34  #Fact    : 0
% 2.52/1.34  #Define  : 0
% 2.52/1.34  #Split   : 4
% 2.52/1.34  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.34  
% 2.52/1.34  Ordering : KBO
% 2.52/1.34  
% 2.52/1.34  Simplification rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Subsume      : 6
% 2.52/1.34  #Demod        : 38
% 2.52/1.34  #Tautology    : 39
% 2.52/1.34  #SimpNegUnit  : 2
% 2.52/1.34  #BackRed      : 1
% 2.52/1.34  
% 2.52/1.34  #Partial instantiations: 0
% 2.52/1.34  #Strategies tried      : 1
% 2.52/1.34  
% 2.52/1.34  Timing (in seconds)
% 2.52/1.34  ----------------------
% 2.52/1.34  Preprocessing        : 0.30
% 2.52/1.34  Parsing              : 0.16
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.26
% 2.52/1.34  Inferencing          : 0.10
% 2.52/1.34  Reduction            : 0.08
% 2.52/1.34  Demodulation         : 0.05
% 2.52/1.34  BG Simplification    : 0.01
% 2.52/1.34  Subsumption          : 0.04
% 2.52/1.34  Abstraction          : 0.02
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.59
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
