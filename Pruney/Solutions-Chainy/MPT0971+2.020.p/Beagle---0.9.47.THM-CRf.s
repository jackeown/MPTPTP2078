%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:32 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 163 expanded)
%              Number of leaves         :   35 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 383 expanded)
%              Number of equality atoms :   15 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_58,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_64,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_61])).

tff(c_91,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_95,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_91])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_189,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden(k4_tarski('#skF_2'(A_85,B_86,C_87),A_85),C_87)
      | ~ r2_hidden(A_85,k9_relat_1(C_87,B_86))
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( k1_funct_1(C_22,A_20) = B_21
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_248,plain,(
    ! [C_94,A_95,B_96] :
      ( k1_funct_1(C_94,'#skF_2'(A_95,B_96,C_94)) = A_95
      | ~ v1_funct_1(C_94)
      | ~ r2_hidden(A_95,k9_relat_1(C_94,B_96))
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_189,c_28])).

tff(c_268,plain,(
    ! [A_19,A_95] :
      ( k1_funct_1(A_19,'#skF_2'(A_95,k1_relat_1(A_19),A_19)) = A_95
      | ~ v1_funct_1(A_19)
      | ~ r2_hidden(A_95,k2_relat_1(A_19))
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_248])).

tff(c_152,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_2'(A_70,B_71,C_72),B_71)
      | ~ r2_hidden(A_70,k9_relat_1(C_72,B_71))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_234,plain,(
    ! [A_90,B_91,C_92,B_93] :
      ( r2_hidden('#skF_2'(A_90,B_91,C_92),B_93)
      | ~ r1_tarski(B_91,B_93)
      | ~ r2_hidden(A_90,k9_relat_1(C_92,B_91))
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_38,plain,(
    ! [E_30] :
      ( k1_funct_1('#skF_6',E_30) != '#skF_5'
      | ~ r2_hidden(E_30,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_294,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_funct_1('#skF_6','#skF_2'(A_101,B_102,C_103)) != '#skF_5'
      | ~ r1_tarski(B_102,'#skF_3')
      | ~ r2_hidden(A_101,k9_relat_1(C_103,B_102))
      | ~ v1_relat_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_234,c_38])).

tff(c_628,plain,(
    ! [A_165,A_166] :
      ( k1_funct_1('#skF_6','#skF_2'(A_165,k1_relat_1(A_166),A_166)) != '#skF_5'
      | ~ r1_tarski(k1_relat_1(A_166),'#skF_3')
      | ~ r2_hidden(A_165,k2_relat_1(A_166))
      | ~ v1_relat_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_294])).

tff(c_632,plain,(
    ! [A_95] :
      ( A_95 != '#skF_5'
      | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
      | ~ r2_hidden(A_95,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_95,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_628])).

tff(c_634,plain,(
    ! [A_95] :
      ( A_95 != '#skF_5'
      | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
      | ~ r2_hidden(A_95,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_46,c_64,c_64,c_632])).

tff(c_635,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_662,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_635])).

tff(c_666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_95,c_662])).

tff(c_690,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_129,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_133,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_129])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_135,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_40])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_690,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.75/1.43  
% 2.75/1.43  %Foreground sorts:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Background operators:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Foreground operators:
% 2.75/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.75/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.75/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.75/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.75/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.75/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.75/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.43  
% 2.75/1.45  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.75/1.45  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.75/1.45  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.75/1.45  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.75/1.45  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.75/1.45  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.75/1.45  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.75/1.45  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.75/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.75/1.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.75/1.45  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.45  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.75/1.45  tff(c_58, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.45  tff(c_61, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.75/1.45  tff(c_64, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_61])).
% 2.75/1.45  tff(c_91, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.45  tff(c_95, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_91])).
% 2.75/1.45  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.75/1.45  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.75/1.45  tff(c_24, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.75/1.45  tff(c_189, plain, (![A_85, B_86, C_87]: (r2_hidden(k4_tarski('#skF_2'(A_85, B_86, C_87), A_85), C_87) | ~r2_hidden(A_85, k9_relat_1(C_87, B_86)) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.45  tff(c_28, plain, (![C_22, A_20, B_21]: (k1_funct_1(C_22, A_20)=B_21 | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.45  tff(c_248, plain, (![C_94, A_95, B_96]: (k1_funct_1(C_94, '#skF_2'(A_95, B_96, C_94))=A_95 | ~v1_funct_1(C_94) | ~r2_hidden(A_95, k9_relat_1(C_94, B_96)) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_189, c_28])).
% 2.75/1.45  tff(c_268, plain, (![A_19, A_95]: (k1_funct_1(A_19, '#skF_2'(A_95, k1_relat_1(A_19), A_19))=A_95 | ~v1_funct_1(A_19) | ~r2_hidden(A_95, k2_relat_1(A_19)) | ~v1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_248])).
% 2.75/1.45  tff(c_152, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_2'(A_70, B_71, C_72), B_71) | ~r2_hidden(A_70, k9_relat_1(C_72, B_71)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.75/1.45  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.45  tff(c_234, plain, (![A_90, B_91, C_92, B_93]: (r2_hidden('#skF_2'(A_90, B_91, C_92), B_93) | ~r1_tarski(B_91, B_93) | ~r2_hidden(A_90, k9_relat_1(C_92, B_91)) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_152, c_2])).
% 2.75/1.45  tff(c_38, plain, (![E_30]: (k1_funct_1('#skF_6', E_30)!='#skF_5' | ~r2_hidden(E_30, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.75/1.45  tff(c_294, plain, (![A_101, B_102, C_103]: (k1_funct_1('#skF_6', '#skF_2'(A_101, B_102, C_103))!='#skF_5' | ~r1_tarski(B_102, '#skF_3') | ~r2_hidden(A_101, k9_relat_1(C_103, B_102)) | ~v1_relat_1(C_103))), inference(resolution, [status(thm)], [c_234, c_38])).
% 2.75/1.45  tff(c_628, plain, (![A_165, A_166]: (k1_funct_1('#skF_6', '#skF_2'(A_165, k1_relat_1(A_166), A_166))!='#skF_5' | ~r1_tarski(k1_relat_1(A_166), '#skF_3') | ~r2_hidden(A_165, k2_relat_1(A_166)) | ~v1_relat_1(A_166) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_24, c_294])).
% 2.75/1.45  tff(c_632, plain, (![A_95]: (A_95!='#skF_5' | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~r2_hidden(A_95, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~r2_hidden(A_95, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_628])).
% 2.75/1.45  tff(c_634, plain, (![A_95]: (A_95!='#skF_5' | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~r2_hidden(A_95, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_46, c_64, c_64, c_632])).
% 2.75/1.45  tff(c_635, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_634])).
% 2.75/1.45  tff(c_662, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_635])).
% 2.75/1.45  tff(c_666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_95, c_662])).
% 2.75/1.45  tff(c_690, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_634])).
% 2.75/1.45  tff(c_129, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.75/1.45  tff(c_133, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_129])).
% 2.75/1.45  tff(c_40, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.75/1.45  tff(c_135, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_40])).
% 2.75/1.45  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_690, c_135])).
% 2.75/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  Inference rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Ref     : 0
% 2.75/1.45  #Sup     : 143
% 2.75/1.45  #Fact    : 0
% 2.75/1.45  #Define  : 0
% 2.75/1.45  #Split   : 2
% 2.75/1.45  #Chain   : 0
% 2.75/1.45  #Close   : 0
% 2.75/1.45  
% 2.75/1.45  Ordering : KBO
% 2.75/1.45  
% 2.75/1.45  Simplification rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Subsume      : 10
% 2.75/1.45  #Demod        : 14
% 2.75/1.45  #Tautology    : 15
% 2.75/1.45  #SimpNegUnit  : 1
% 2.75/1.45  #BackRed      : 3
% 2.75/1.45  
% 2.75/1.45  #Partial instantiations: 0
% 2.75/1.45  #Strategies tried      : 1
% 2.75/1.45  
% 2.75/1.45  Timing (in seconds)
% 2.75/1.45  ----------------------
% 2.75/1.45  Preprocessing        : 0.33
% 2.75/1.45  Parsing              : 0.17
% 2.75/1.45  CNF conversion       : 0.02
% 2.75/1.45  Main loop            : 0.37
% 2.75/1.45  Inferencing          : 0.14
% 2.75/1.45  Reduction            : 0.09
% 2.75/1.45  Demodulation         : 0.07
% 2.75/1.45  BG Simplification    : 0.02
% 2.75/1.45  Subsumption          : 0.09
% 2.75/1.45  Abstraction          : 0.02
% 2.75/1.45  MUC search           : 0.00
% 2.75/1.45  Cooper               : 0.00
% 2.75/1.45  Total                : 0.73
% 2.75/1.45  Index Insertion      : 0.00
% 2.75/1.45  Index Deletion       : 0.00
% 2.75/1.45  Index Matching       : 0.00
% 2.75/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
