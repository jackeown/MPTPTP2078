%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:26 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 127 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_41,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_101,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39,c_101])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [A_4,A_40,B_41] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_40,B_41)) ) ),
    inference(resolution,[status(thm)],[c_6,c_41])).

tff(c_140,plain,(
    ! [A_60] :
      ( v1_relat_1(A_60)
      | ~ r1_tarski(A_60,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_128,c_49])).

tff(c_148,plain,(
    ! [A_11] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_11))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_152,plain,(
    ! [A_11] : v1_relat_1(k7_relat_1('#skF_4',A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_148])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_14,A_13)),k2_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_114,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_157,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k2_relset_1(A_68,B_69,C_70),k1_zfmisc_1(B_69))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_174,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_157])).

tff(c_180,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,'#skF_3')
      | ~ r1_tarski(A_73,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_188,c_2])).

tff(c_221,plain,(
    ! [A_13] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_13)),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_217])).

tff(c_232,plain,(
    ! [A_13] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_13)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_221])).

tff(c_315,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ r1_tarski(k2_relat_1(C_85),B_87)
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_247,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k5_relset_1(A_75,B_76,C_77,D_78) = k7_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_258,plain,(
    ! [D_78] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_78) = k7_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_28,c_247])).

tff(c_26,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_260,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_26])).

tff(c_318,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_315,c_260])).

tff(c_335,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_232,c_318])).

tff(c_343,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_335])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.29  
% 2.31/1.29  %Foreground sorts:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Background operators:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Foreground operators:
% 2.31/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.31/1.29  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.29  
% 2.31/1.31  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.31/1.31  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.31/1.31  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.31/1.31  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.31/1.31  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.31/1.31  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.31/1.31  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 2.31/1.31  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.31/1.31  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.31/1.31  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.31/1.31  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.31/1.31  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.31/1.31  tff(c_41, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.31/1.31  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_41])).
% 2.31/1.31  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.31  tff(c_12, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.31/1.31  tff(c_31, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.31  tff(c_39, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.31/1.31  tff(c_101, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.31  tff(c_128, plain, (![A_59]: (r1_tarski(A_59, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_59, '#skF_4'))), inference(resolution, [status(thm)], [c_39, c_101])).
% 2.31/1.31  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.31  tff(c_49, plain, (![A_4, A_40, B_41]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_40, B_41)))), inference(resolution, [status(thm)], [c_6, c_41])).
% 2.31/1.31  tff(c_140, plain, (![A_60]: (v1_relat_1(A_60) | ~r1_tarski(A_60, '#skF_4'))), inference(resolution, [status(thm)], [c_128, c_49])).
% 2.31/1.31  tff(c_148, plain, (![A_11]: (v1_relat_1(k7_relat_1('#skF_4', A_11)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_140])).
% 2.31/1.31  tff(c_152, plain, (![A_11]: (v1_relat_1(k7_relat_1('#skF_4', A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_148])).
% 2.31/1.31  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(k7_relat_1(B_14, A_13)), k2_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.31/1.31  tff(c_114, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.31/1.31  tff(c_123, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.31/1.31  tff(c_157, plain, (![A_68, B_69, C_70]: (m1_subset_1(k2_relset_1(A_68, B_69, C_70), k1_zfmisc_1(B_69)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.31  tff(c_174, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_157])).
% 2.31/1.31  tff(c_180, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_174])).
% 2.31/1.31  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.31  tff(c_188, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_180, c_4])).
% 2.31/1.31  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.31  tff(c_217, plain, (![A_73]: (r1_tarski(A_73, '#skF_3') | ~r1_tarski(A_73, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_188, c_2])).
% 2.31/1.31  tff(c_221, plain, (![A_13]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_13)), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_217])).
% 2.31/1.31  tff(c_232, plain, (![A_13]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_13)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_221])).
% 2.31/1.31  tff(c_315, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~r1_tarski(k2_relat_1(C_85), B_87) | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.31/1.31  tff(c_247, plain, (![A_75, B_76, C_77, D_78]: (k5_relset_1(A_75, B_76, C_77, D_78)=k7_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.31/1.31  tff(c_258, plain, (![D_78]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_78)=k7_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_28, c_247])).
% 2.31/1.31  tff(c_26, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.31/1.31  tff(c_260, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_26])).
% 2.31/1.31  tff(c_318, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_315, c_260])).
% 2.31/1.31  tff(c_335, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_232, c_318])).
% 2.31/1.31  tff(c_343, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_335])).
% 2.31/1.31  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_343])).
% 2.31/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  
% 2.31/1.31  Inference rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Ref     : 0
% 2.31/1.31  #Sup     : 70
% 2.31/1.31  #Fact    : 0
% 2.31/1.31  #Define  : 0
% 2.31/1.31  #Split   : 3
% 2.31/1.31  #Chain   : 0
% 2.31/1.31  #Close   : 0
% 2.31/1.31  
% 2.31/1.31  Ordering : KBO
% 2.31/1.31  
% 2.31/1.31  Simplification rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Subsume      : 9
% 2.31/1.31  #Demod        : 13
% 2.31/1.31  #Tautology    : 11
% 2.31/1.31  #SimpNegUnit  : 0
% 2.31/1.31  #BackRed      : 2
% 2.31/1.31  
% 2.31/1.31  #Partial instantiations: 0
% 2.31/1.31  #Strategies tried      : 1
% 2.31/1.31  
% 2.31/1.31  Timing (in seconds)
% 2.31/1.31  ----------------------
% 2.31/1.31  Preprocessing        : 0.30
% 2.31/1.31  Parsing              : 0.16
% 2.31/1.31  CNF conversion       : 0.02
% 2.31/1.31  Main loop            : 0.25
% 2.31/1.31  Inferencing          : 0.10
% 2.31/1.31  Reduction            : 0.07
% 2.31/1.31  Demodulation         : 0.05
% 2.31/1.31  BG Simplification    : 0.01
% 2.31/1.31  Subsumption          : 0.05
% 2.31/1.31  Abstraction          : 0.01
% 2.31/1.31  MUC search           : 0.00
% 2.31/1.31  Cooper               : 0.00
% 2.31/1.31  Total                : 0.58
% 2.31/1.31  Index Insertion      : 0.00
% 2.31/1.31  Index Deletion       : 0.00
% 2.31/1.31  Index Matching       : 0.00
% 2.31/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
