%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:02 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   63 (  91 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 176 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_1'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_186,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_197,plain,(
    ! [D_95] : k7_relset_1('#skF_4','#skF_5','#skF_6',D_95) = k9_relat_1('#skF_6',D_95) ),
    inference(resolution,[status(thm)],[c_40,c_186])).

tff(c_359,plain,(
    ! [A_131,B_132,C_133] :
      ( k7_relset_1(A_131,B_132,C_133,A_131) = k2_relset_1(A_131,B_132,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_367,plain,(
    k7_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') = k2_relset_1('#skF_4','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_359])).

tff(c_371,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k9_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_367])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_376,plain,(
    r2_hidden('#skF_3',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_38])).

tff(c_207,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden(k4_tarski('#skF_2'(A_97,B_98,C_99),A_97),C_99)
      | ~ r2_hidden(A_97,k9_relat_1(C_99,B_98))
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [C_19,A_17,B_18] :
      ( k1_funct_1(C_19,A_17) = B_18
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_587,plain,(
    ! [C_165,A_166,B_167] :
      ( k1_funct_1(C_165,'#skF_2'(A_166,B_167,C_165)) = A_166
      | ~ v1_funct_1(C_165)
      | ~ r2_hidden(A_166,k9_relat_1(C_165,B_167))
      | ~ v1_relat_1(C_165) ) ),
    inference(resolution,[status(thm)],[c_207,c_24])).

tff(c_594,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_376,c_587])).

tff(c_614,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_594])).

tff(c_154,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_2'(A_71,B_72,C_73),B_72)
      | ~ r2_hidden(A_71,k9_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_54,B_7,A_6] :
      ( m1_subset_1(A_54,B_7)
      | ~ r2_hidden(A_54,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_100])).

tff(c_1477,plain,(
    ! [A_239,B_240,C_241,B_242] :
      ( m1_subset_1('#skF_2'(A_239,B_240,C_241),B_242)
      | ~ r1_tarski(B_240,B_242)
      | ~ r2_hidden(A_239,k9_relat_1(C_241,B_240))
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_154,c_105])).

tff(c_1507,plain,(
    ! [B_242] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),B_242)
      | ~ r1_tarski('#skF_4',B_242)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_376,c_1477])).

tff(c_1543,plain,(
    ! [B_243] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),B_243)
      | ~ r1_tarski('#skF_4',B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1507])).

tff(c_36,plain,(
    ! [E_31] :
      ( k1_funct_1('#skF_6',E_31) != '#skF_3'
      | ~ m1_subset_1(E_31,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1563,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1543,c_36])).

tff(c_1576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_614,c_1563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.62  
% 3.80/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.62  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.80/1.62  
% 3.80/1.62  %Foreground sorts:
% 3.80/1.62  
% 3.80/1.62  
% 3.80/1.62  %Background operators:
% 3.80/1.62  
% 3.80/1.62  
% 3.80/1.62  %Foreground operators:
% 3.80/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.80/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.80/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.80/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.80/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.80/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.80/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.80/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.80/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.80/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.62  
% 3.80/1.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.80/1.63  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.80/1.63  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.80/1.63  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.80/1.63  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.80/1.63  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.80/1.63  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.80/1.63  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.80/1.63  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.80/1.63  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_73, plain, (![A_45, B_46]: (~r2_hidden('#skF_1'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_78, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_73])).
% 3.80/1.63  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.80/1.63  tff(c_57, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.80/1.63  tff(c_66, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_57])).
% 3.80/1.63  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.80/1.63  tff(c_186, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.80/1.63  tff(c_197, plain, (![D_95]: (k7_relset_1('#skF_4', '#skF_5', '#skF_6', D_95)=k9_relat_1('#skF_6', D_95))), inference(resolution, [status(thm)], [c_40, c_186])).
% 3.80/1.63  tff(c_359, plain, (![A_131, B_132, C_133]: (k7_relset_1(A_131, B_132, C_133, A_131)=k2_relset_1(A_131, B_132, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.80/1.63  tff(c_367, plain, (k7_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')=k2_relset_1('#skF_4', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_359])).
% 3.80/1.63  tff(c_371, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k9_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_367])).
% 3.80/1.63  tff(c_38, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.80/1.63  tff(c_376, plain, (r2_hidden('#skF_3', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_38])).
% 3.80/1.63  tff(c_207, plain, (![A_97, B_98, C_99]: (r2_hidden(k4_tarski('#skF_2'(A_97, B_98, C_99), A_97), C_99) | ~r2_hidden(A_97, k9_relat_1(C_99, B_98)) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.80/1.63  tff(c_24, plain, (![C_19, A_17, B_18]: (k1_funct_1(C_19, A_17)=B_18 | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.80/1.63  tff(c_587, plain, (![C_165, A_166, B_167]: (k1_funct_1(C_165, '#skF_2'(A_166, B_167, C_165))=A_166 | ~v1_funct_1(C_165) | ~r2_hidden(A_166, k9_relat_1(C_165, B_167)) | ~v1_relat_1(C_165))), inference(resolution, [status(thm)], [c_207, c_24])).
% 3.80/1.63  tff(c_594, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_376, c_587])).
% 3.80/1.63  tff(c_614, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_594])).
% 3.80/1.63  tff(c_154, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_2'(A_71, B_72, C_73), B_72) | ~r2_hidden(A_71, k9_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.80/1.63  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.80/1.63  tff(c_100, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.80/1.63  tff(c_105, plain, (![A_54, B_7, A_6]: (m1_subset_1(A_54, B_7) | ~r2_hidden(A_54, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_100])).
% 3.80/1.63  tff(c_1477, plain, (![A_239, B_240, C_241, B_242]: (m1_subset_1('#skF_2'(A_239, B_240, C_241), B_242) | ~r1_tarski(B_240, B_242) | ~r2_hidden(A_239, k9_relat_1(C_241, B_240)) | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_154, c_105])).
% 3.80/1.63  tff(c_1507, plain, (![B_242]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), B_242) | ~r1_tarski('#skF_4', B_242) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_376, c_1477])).
% 3.80/1.63  tff(c_1543, plain, (![B_243]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), B_243) | ~r1_tarski('#skF_4', B_243))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1507])).
% 3.80/1.63  tff(c_36, plain, (![E_31]: (k1_funct_1('#skF_6', E_31)!='#skF_3' | ~m1_subset_1(E_31, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.80/1.63  tff(c_1563, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1543, c_36])).
% 3.80/1.63  tff(c_1576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_614, c_1563])).
% 3.80/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.63  
% 3.80/1.63  Inference rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Ref     : 0
% 3.80/1.63  #Sup     : 359
% 3.80/1.63  #Fact    : 0
% 3.80/1.63  #Define  : 0
% 3.80/1.63  #Split   : 12
% 3.80/1.63  #Chain   : 0
% 3.80/1.63  #Close   : 0
% 3.80/1.63  
% 3.80/1.63  Ordering : KBO
% 3.80/1.63  
% 3.80/1.63  Simplification rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Subsume      : 29
% 3.80/1.63  #Demod        : 85
% 3.80/1.63  #Tautology    : 42
% 3.80/1.63  #SimpNegUnit  : 0
% 3.80/1.63  #BackRed      : 5
% 3.80/1.63  
% 3.80/1.63  #Partial instantiations: 0
% 3.80/1.63  #Strategies tried      : 1
% 3.80/1.63  
% 3.80/1.63  Timing (in seconds)
% 3.80/1.63  ----------------------
% 3.80/1.64  Preprocessing        : 0.31
% 3.80/1.64  Parsing              : 0.17
% 3.80/1.64  CNF conversion       : 0.02
% 3.80/1.64  Main loop            : 0.56
% 3.80/1.64  Inferencing          : 0.20
% 3.80/1.64  Reduction            : 0.16
% 3.80/1.64  Demodulation         : 0.11
% 3.80/1.64  BG Simplification    : 0.03
% 3.80/1.64  Subsumption          : 0.13
% 3.80/1.64  Abstraction          : 0.03
% 3.80/1.64  MUC search           : 0.00
% 3.80/1.64  Cooper               : 0.00
% 3.80/1.64  Total                : 0.90
% 3.80/1.64  Index Insertion      : 0.00
% 3.80/1.64  Index Deletion       : 0.00
% 3.80/1.64  Index Matching       : 0.00
% 3.80/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
