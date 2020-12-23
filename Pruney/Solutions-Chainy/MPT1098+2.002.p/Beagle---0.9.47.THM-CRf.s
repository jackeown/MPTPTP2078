%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 185 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_46,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_200,plain,(
    ! [A_71,B_72,C_73] :
      ( v1_finset_1('#skF_1'(A_71,B_72,C_73))
      | ~ r1_tarski(A_71,k2_zfmisc_1(B_72,C_73))
      | ~ v1_finset_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_211,plain,
    ( v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_200])).

tff(c_220,plain,(
    v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_211])).

tff(c_38,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski('#skF_1'(A_22,B_23,C_24),B_23)
      | ~ r1_tarski(A_22,k2_zfmisc_1(B_23,C_24))
      | ~ v1_finset_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_414,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(A_115,k2_zfmisc_1('#skF_1'(A_115,B_116,C_117),'#skF_2'(A_115,B_116,C_117)))
      | ~ r1_tarski(A_115,k2_zfmisc_1(B_116,C_117))
      | ~ v1_finset_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_173,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_178,plain,(
    ! [A_3,A_64,B_65] :
      ( v4_relat_1(A_3,A_64)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_64,B_65)) ) ),
    inference(resolution,[status(thm)],[c_10,c_173])).

tff(c_445,plain,(
    ! [A_115,B_116,C_117] :
      ( v4_relat_1(A_115,'#skF_1'(A_115,B_116,C_117))
      | ~ r1_tarski(A_115,k2_zfmisc_1(B_116,C_117))
      | ~ v1_finset_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_414,c_178])).

tff(c_22,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(A_43)
      | ~ v1_relat_1(B_44)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_91,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_88])).

tff(c_97,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_91])).

tff(c_146,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_152,plain,(
    ! [A_58,B_59,A_60] :
      ( v5_relat_1(A_58,B_59)
      | ~ r1_tarski(A_58,k2_zfmisc_1(A_60,B_59)) ) ),
    inference(resolution,[status(thm)],[c_10,c_146])).

tff(c_170,plain,(
    v5_relat_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_152])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_371,plain,(
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ r1_tarski(k2_relat_1(C_99),B_101)
      | ~ r1_tarski(k1_relat_1(C_99),A_100)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_621,plain,(
    ! [C_143,A_144,B_145] :
      ( r1_tarski(C_143,k2_zfmisc_1(A_144,B_145))
      | ~ r1_tarski(k2_relat_1(C_143),B_145)
      | ~ r1_tarski(k1_relat_1(C_143),A_144)
      | ~ v1_relat_1(C_143) ) ),
    inference(resolution,[status(thm)],[c_371,c_8])).

tff(c_766,plain,(
    ! [B_164,A_165,A_166] :
      ( r1_tarski(B_164,k2_zfmisc_1(A_165,A_166))
      | ~ r1_tarski(k1_relat_1(B_164),A_165)
      | ~ v5_relat_1(B_164,A_166)
      | ~ v1_relat_1(B_164) ) ),
    inference(resolution,[status(thm)],[c_20,c_621])).

tff(c_848,plain,(
    ! [B_174,A_175,A_176] :
      ( r1_tarski(B_174,k2_zfmisc_1(A_175,A_176))
      | ~ v5_relat_1(B_174,A_176)
      | ~ v4_relat_1(B_174,A_175)
      | ~ v1_relat_1(B_174) ) ),
    inference(resolution,[status(thm)],[c_16,c_766])).

tff(c_42,plain,(
    ! [D_28] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_28,'#skF_5'))
      | ~ r1_tarski(D_28,'#skF_4')
      | ~ v1_finset_1(D_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_887,plain,(
    ! [A_175] :
      ( ~ r1_tarski(A_175,'#skF_4')
      | ~ v1_finset_1(A_175)
      | ~ v5_relat_1('#skF_3','#skF_5')
      | ~ v4_relat_1('#skF_3',A_175)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_848,c_42])).

tff(c_911,plain,(
    ! [A_177] :
      ( ~ r1_tarski(A_177,'#skF_4')
      | ~ v1_finset_1(A_177)
      | ~ v4_relat_1('#skF_3',A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_170,c_887])).

tff(c_915,plain,(
    ! [B_116,C_117] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_116,C_117),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_116,C_117))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_116,C_117))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_445,c_911])).

tff(c_987,plain,(
    ! [B_197,C_198] :
      ( ~ r1_tarski('#skF_1'('#skF_3',B_197,C_198),'#skF_4')
      | ~ v1_finset_1('#skF_1'('#skF_3',B_197,C_198))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(B_197,C_198)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_915])).

tff(c_991,plain,(
    ! [C_24] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_24))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_24))
      | ~ v1_finset_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_987])).

tff(c_995,plain,(
    ! [C_199] :
      ( ~ v1_finset_1('#skF_1'('#skF_3','#skF_4',C_199))
      | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4',C_199)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_991])).

tff(c_1006,plain,(
    ~ v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_995])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:51:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.44  
% 2.89/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_finset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.89/1.45  
% 2.89/1.45  %Foreground sorts:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Background operators:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Foreground operators:
% 2.89/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.89/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.45  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.89/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.45  
% 3.17/1.46  tff(f_107, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_finset_1)).
% 3.17/1.46  tff(f_93, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_finset_1)).
% 3.17/1.46  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.17/1.46  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.17/1.46  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.17/1.46  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.17/1.46  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.17/1.46  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.17/1.46  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.17/1.46  tff(c_46, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.46  tff(c_44, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.46  tff(c_200, plain, (![A_71, B_72, C_73]: (v1_finset_1('#skF_1'(A_71, B_72, C_73)) | ~r1_tarski(A_71, k2_zfmisc_1(B_72, C_73)) | ~v1_finset_1(A_71))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.17/1.46  tff(c_211, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_200])).
% 3.17/1.46  tff(c_220, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_211])).
% 3.17/1.46  tff(c_38, plain, (![A_22, B_23, C_24]: (r1_tarski('#skF_1'(A_22, B_23, C_24), B_23) | ~r1_tarski(A_22, k2_zfmisc_1(B_23, C_24)) | ~v1_finset_1(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.17/1.46  tff(c_414, plain, (![A_115, B_116, C_117]: (r1_tarski(A_115, k2_zfmisc_1('#skF_1'(A_115, B_116, C_117), '#skF_2'(A_115, B_116, C_117))) | ~r1_tarski(A_115, k2_zfmisc_1(B_116, C_117)) | ~v1_finset_1(A_115))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.17/1.46  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.46  tff(c_173, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.46  tff(c_178, plain, (![A_3, A_64, B_65]: (v4_relat_1(A_3, A_64) | ~r1_tarski(A_3, k2_zfmisc_1(A_64, B_65)))), inference(resolution, [status(thm)], [c_10, c_173])).
% 3.17/1.46  tff(c_445, plain, (![A_115, B_116, C_117]: (v4_relat_1(A_115, '#skF_1'(A_115, B_116, C_117)) | ~r1_tarski(A_115, k2_zfmisc_1(B_116, C_117)) | ~v1_finset_1(A_115))), inference(resolution, [status(thm)], [c_414, c_178])).
% 3.17/1.46  tff(c_22, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.46  tff(c_76, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.17/1.46  tff(c_88, plain, (![A_43, B_44]: (v1_relat_1(A_43) | ~v1_relat_1(B_44) | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_10, c_76])).
% 3.17/1.46  tff(c_91, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_88])).
% 3.17/1.46  tff(c_97, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_91])).
% 3.17/1.46  tff(c_146, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.17/1.46  tff(c_152, plain, (![A_58, B_59, A_60]: (v5_relat_1(A_58, B_59) | ~r1_tarski(A_58, k2_zfmisc_1(A_60, B_59)))), inference(resolution, [status(thm)], [c_10, c_146])).
% 3.17/1.46  tff(c_170, plain, (v5_relat_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_152])).
% 3.17/1.46  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.17/1.46  tff(c_20, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.17/1.46  tff(c_371, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~r1_tarski(k2_relat_1(C_99), B_101) | ~r1_tarski(k1_relat_1(C_99), A_100) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.46  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.46  tff(c_621, plain, (![C_143, A_144, B_145]: (r1_tarski(C_143, k2_zfmisc_1(A_144, B_145)) | ~r1_tarski(k2_relat_1(C_143), B_145) | ~r1_tarski(k1_relat_1(C_143), A_144) | ~v1_relat_1(C_143))), inference(resolution, [status(thm)], [c_371, c_8])).
% 3.17/1.46  tff(c_766, plain, (![B_164, A_165, A_166]: (r1_tarski(B_164, k2_zfmisc_1(A_165, A_166)) | ~r1_tarski(k1_relat_1(B_164), A_165) | ~v5_relat_1(B_164, A_166) | ~v1_relat_1(B_164))), inference(resolution, [status(thm)], [c_20, c_621])).
% 3.17/1.46  tff(c_848, plain, (![B_174, A_175, A_176]: (r1_tarski(B_174, k2_zfmisc_1(A_175, A_176)) | ~v5_relat_1(B_174, A_176) | ~v4_relat_1(B_174, A_175) | ~v1_relat_1(B_174))), inference(resolution, [status(thm)], [c_16, c_766])).
% 3.17/1.46  tff(c_42, plain, (![D_28]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_28, '#skF_5')) | ~r1_tarski(D_28, '#skF_4') | ~v1_finset_1(D_28))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.46  tff(c_887, plain, (![A_175]: (~r1_tarski(A_175, '#skF_4') | ~v1_finset_1(A_175) | ~v5_relat_1('#skF_3', '#skF_5') | ~v4_relat_1('#skF_3', A_175) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_848, c_42])).
% 3.17/1.46  tff(c_911, plain, (![A_177]: (~r1_tarski(A_177, '#skF_4') | ~v1_finset_1(A_177) | ~v4_relat_1('#skF_3', A_177))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_170, c_887])).
% 3.17/1.46  tff(c_915, plain, (![B_116, C_117]: (~r1_tarski('#skF_1'('#skF_3', B_116, C_117), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_116, C_117)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_116, C_117)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_445, c_911])).
% 3.17/1.46  tff(c_987, plain, (![B_197, C_198]: (~r1_tarski('#skF_1'('#skF_3', B_197, C_198), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', B_197, C_198)) | ~r1_tarski('#skF_3', k2_zfmisc_1(B_197, C_198)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_915])).
% 3.17/1.46  tff(c_991, plain, (![C_24]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_24)) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_24)) | ~v1_finset_1('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_987])).
% 3.17/1.46  tff(c_995, plain, (![C_199]: (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', C_199)) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', C_199)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_991])).
% 3.17/1.46  tff(c_1006, plain, (~v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_995])).
% 3.17/1.46  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_1006])).
% 3.17/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.46  
% 3.17/1.46  Inference rules
% 3.17/1.46  ----------------------
% 3.17/1.46  #Ref     : 0
% 3.17/1.46  #Sup     : 194
% 3.17/1.46  #Fact    : 0
% 3.17/1.46  #Define  : 0
% 3.17/1.46  #Split   : 5
% 3.17/1.46  #Chain   : 0
% 3.17/1.46  #Close   : 0
% 3.17/1.46  
% 3.17/1.46  Ordering : KBO
% 3.17/1.46  
% 3.17/1.46  Simplification rules
% 3.17/1.46  ----------------------
% 3.17/1.46  #Subsume      : 13
% 3.17/1.46  #Demod        : 43
% 3.17/1.46  #Tautology    : 27
% 3.17/1.46  #SimpNegUnit  : 0
% 3.17/1.46  #BackRed      : 0
% 3.17/1.46  
% 3.17/1.46  #Partial instantiations: 0
% 3.17/1.46  #Strategies tried      : 1
% 3.21/1.46  
% 3.21/1.46  Timing (in seconds)
% 3.21/1.46  ----------------------
% 3.21/1.46  Preprocessing        : 0.29
% 3.21/1.46  Parsing              : 0.17
% 3.21/1.46  CNF conversion       : 0.02
% 3.21/1.46  Main loop            : 0.40
% 3.21/1.46  Inferencing          : 0.16
% 3.21/1.46  Reduction            : 0.11
% 3.21/1.46  Demodulation         : 0.08
% 3.21/1.46  BG Simplification    : 0.02
% 3.21/1.46  Subsumption          : 0.09
% 3.21/1.46  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.73
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
