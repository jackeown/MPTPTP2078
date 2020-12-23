%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:19 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 241 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1017,plain,(
    ! [A_183,B_184,C_185] :
      ( k2_relset_1(A_183,B_184,C_185) = k2_relat_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1026,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1017])).

tff(c_253,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_262,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_253])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_263,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_72])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_97,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_93])).

tff(c_129,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_129])).

tff(c_38,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(A_41)
      | ~ v1_relat_1(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_117,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_126,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_117])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_294,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k1_relat_1(A_81),k1_relat_1(B_82))
      | ~ r1_tarski(A_81,B_82)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_580,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(A_116,k1_relat_1(B_117))
      | ~ r1_tarski(k6_relat_1(A_116),B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(k6_relat_1(A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_294])).

tff(c_583,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_580])).

tff(c_590,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_97,c_583])).

tff(c_174,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [B_60,A_61] :
      ( k1_relat_1(B_60) = A_61
      | ~ r1_tarski(A_61,k1_relat_1(B_60))
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_595,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_590,c_198])).

tff(c_603,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_138,c_595])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_603])).

tff(c_606,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1027,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_606])).

tff(c_626,plain,(
    ! [B_120,A_121] :
      ( v1_relat_1(B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_121))
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_632,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_626])).

tff(c_636,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_632])).

tff(c_637,plain,(
    ! [A_122,B_123] :
      ( v1_relat_1(A_122)
      | ~ v1_relat_1(B_123)
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_10,c_626])).

tff(c_643,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_637])).

tff(c_652,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_643])).

tff(c_26,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_737,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k2_relat_1(A_144),k2_relat_1(B_145))
      | ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1671,plain,(
    ! [A_228,B_229] :
      ( r1_tarski(A_228,k2_relat_1(B_229))
      | ~ r1_tarski(k6_relat_1(A_228),B_229)
      | ~ v1_relat_1(B_229)
      | ~ v1_relat_1(k6_relat_1(A_228)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_737])).

tff(c_1674,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_1671])).

tff(c_1681,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_636,c_1674])).

tff(c_1683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1027,c_1681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:06:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.55  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.52/1.55  
% 3.52/1.55  %Foreground sorts:
% 3.52/1.55  
% 3.52/1.55  
% 3.52/1.55  %Background operators:
% 3.52/1.55  
% 3.52/1.55  
% 3.52/1.55  %Foreground operators:
% 3.52/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.52/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.55  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.52/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.52/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.55  
% 3.64/1.56  tff(f_88, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relset_1)).
% 3.64/1.56  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.64/1.56  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.64/1.56  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.64/1.56  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.64/1.56  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.64/1.56  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.64/1.56  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.64/1.56  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.64/1.56  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.64/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.64/1.56  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.64/1.56  tff(c_1017, plain, (![A_183, B_184, C_185]: (k2_relset_1(A_183, B_184, C_185)=k2_relat_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.64/1.56  tff(c_1026, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1017])).
% 3.64/1.56  tff(c_253, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.64/1.56  tff(c_262, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_253])).
% 3.64/1.56  tff(c_36, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.64/1.56  tff(c_72, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 3.64/1.56  tff(c_263, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_262, c_72])).
% 3.64/1.56  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.64/1.56  tff(c_87, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.64/1.56  tff(c_93, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_87])).
% 3.64/1.56  tff(c_97, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_93])).
% 3.64/1.56  tff(c_129, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.64/1.56  tff(c_138, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_129])).
% 3.64/1.56  tff(c_38, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.64/1.56  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.56  tff(c_111, plain, (![A_41, B_42]: (v1_relat_1(A_41) | ~v1_relat_1(B_42) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_10, c_87])).
% 3.64/1.56  tff(c_117, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_111])).
% 3.64/1.56  tff(c_126, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_117])).
% 3.64/1.56  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.56  tff(c_294, plain, (![A_81, B_82]: (r1_tarski(k1_relat_1(A_81), k1_relat_1(B_82)) | ~r1_tarski(A_81, B_82) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.64/1.56  tff(c_580, plain, (![A_116, B_117]: (r1_tarski(A_116, k1_relat_1(B_117)) | ~r1_tarski(k6_relat_1(A_116), B_117) | ~v1_relat_1(B_117) | ~v1_relat_1(k6_relat_1(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_294])).
% 3.64/1.56  tff(c_583, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_580])).
% 3.64/1.56  tff(c_590, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_97, c_583])).
% 3.64/1.56  tff(c_174, plain, (![B_60, A_61]: (r1_tarski(k1_relat_1(B_60), A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.64/1.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.56  tff(c_198, plain, (![B_60, A_61]: (k1_relat_1(B_60)=A_61 | ~r1_tarski(A_61, k1_relat_1(B_60)) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_174, c_2])).
% 3.64/1.56  tff(c_595, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_590, c_198])).
% 3.64/1.56  tff(c_603, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_138, c_595])).
% 3.64/1.56  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_603])).
% 3.64/1.56  tff(c_606, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_36])).
% 3.64/1.56  tff(c_1027, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_606])).
% 3.64/1.56  tff(c_626, plain, (![B_120, A_121]: (v1_relat_1(B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_121)) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.64/1.56  tff(c_632, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_626])).
% 3.64/1.56  tff(c_636, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_632])).
% 3.64/1.56  tff(c_637, plain, (![A_122, B_123]: (v1_relat_1(A_122) | ~v1_relat_1(B_123) | ~r1_tarski(A_122, B_123))), inference(resolution, [status(thm)], [c_10, c_626])).
% 3.64/1.56  tff(c_643, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_637])).
% 3.64/1.56  tff(c_652, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_643])).
% 3.64/1.56  tff(c_26, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.56  tff(c_737, plain, (![A_144, B_145]: (r1_tarski(k2_relat_1(A_144), k2_relat_1(B_145)) | ~r1_tarski(A_144, B_145) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.64/1.56  tff(c_1671, plain, (![A_228, B_229]: (r1_tarski(A_228, k2_relat_1(B_229)) | ~r1_tarski(k6_relat_1(A_228), B_229) | ~v1_relat_1(B_229) | ~v1_relat_1(k6_relat_1(A_228)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_737])).
% 3.64/1.56  tff(c_1674, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_1671])).
% 3.64/1.56  tff(c_1681, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_636, c_1674])).
% 3.64/1.56  tff(c_1683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1027, c_1681])).
% 3.64/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.56  
% 3.64/1.56  Inference rules
% 3.64/1.56  ----------------------
% 3.64/1.56  #Ref     : 0
% 3.64/1.56  #Sup     : 329
% 3.64/1.56  #Fact    : 0
% 3.64/1.56  #Define  : 0
% 3.64/1.56  #Split   : 8
% 3.64/1.56  #Chain   : 0
% 3.64/1.56  #Close   : 0
% 3.64/1.56  
% 3.64/1.56  Ordering : KBO
% 3.64/1.56  
% 3.64/1.56  Simplification rules
% 3.64/1.56  ----------------------
% 3.64/1.56  #Subsume      : 49
% 3.64/1.56  #Demod        : 216
% 3.64/1.56  #Tautology    : 95
% 3.64/1.56  #SimpNegUnit  : 7
% 3.64/1.56  #BackRed      : 2
% 3.64/1.56  
% 3.64/1.56  #Partial instantiations: 0
% 3.64/1.56  #Strategies tried      : 1
% 3.64/1.56  
% 3.64/1.56  Timing (in seconds)
% 3.64/1.56  ----------------------
% 3.64/1.57  Preprocessing        : 0.31
% 3.64/1.57  Parsing              : 0.17
% 3.64/1.57  CNF conversion       : 0.02
% 3.64/1.57  Main loop            : 0.50
% 3.64/1.57  Inferencing          : 0.19
% 3.64/1.57  Reduction            : 0.15
% 3.64/1.57  Demodulation         : 0.11
% 3.64/1.57  BG Simplification    : 0.02
% 3.64/1.57  Subsumption          : 0.10
% 3.64/1.57  Abstraction          : 0.03
% 3.64/1.57  MUC search           : 0.00
% 3.64/1.57  Cooper               : 0.00
% 3.64/1.57  Total                : 0.84
% 3.64/1.57  Index Insertion      : 0.00
% 3.64/1.57  Index Deletion       : 0.00
% 3.64/1.57  Index Matching       : 0.00
% 3.64/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
