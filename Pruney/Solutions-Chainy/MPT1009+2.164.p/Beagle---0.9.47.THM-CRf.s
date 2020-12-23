%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:05 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 166 expanded)
%              Number of leaves         :   41 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 333 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_18,plain,(
    ! [A_32,B_33] : v1_relat_1(k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_77,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_77])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_80])).

tff(c_26,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k7_relat_1(B_40,A_39),B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_153,plain,(
    ! [B_95,A_96] :
      ( k1_tarski(k1_funct_1(B_95,A_96)) = k2_relat_1(B_95)
      | k1_tarski(A_96) != k1_relat_1(B_95)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_138,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k7_relset_1(A_88,B_89,C_90,D_91) = k9_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_141,plain,(
    ! [D_91] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_91) = k9_relat_1('#skF_4',D_91) ),
    inference(resolution,[status(thm)],[c_52,c_138])).

tff(c_48,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_142,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_48])).

tff(c_159,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_142])).

tff(c_165,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_159])).

tff(c_168,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_118,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_122,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_118])).

tff(c_248,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_xboole_0 = B_130
      | k1_relset_1(A_131,B_130,C_132) = A_131
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_248])).

tff(c_258,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_122,c_254])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_50,c_258])).

tff(c_262,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_265,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_52])).

tff(c_309,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( m1_subset_1(A_142,k1_zfmisc_1(k2_zfmisc_1(B_143,C_144)))
      | ~ r1_tarski(A_142,D_145)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(B_143,C_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_319,plain,(
    ! [B_146,A_147,B_148,C_149] :
      ( m1_subset_1(k7_relat_1(B_146,A_147),k1_zfmisc_1(k2_zfmisc_1(B_148,C_149)))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k2_zfmisc_1(B_148,C_149)))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_26,c_309])).

tff(c_16,plain,(
    ! [B_31,A_29] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_339,plain,(
    ! [B_146,A_147,B_148,C_149] :
      ( v1_relat_1(k7_relat_1(B_146,A_147))
      | ~ v1_relat_1(k2_zfmisc_1(B_148,C_149))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k2_zfmisc_1(B_148,C_149)))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_319,c_16])).

tff(c_360,plain,(
    ! [B_153,A_154,B_155,C_156] :
      ( v1_relat_1(k7_relat_1(B_153,A_154))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_zfmisc_1(B_155,C_156)))
      | ~ v1_relat_1(B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_339])).

tff(c_364,plain,(
    ! [A_154] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_154))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_265,c_360])).

tff(c_368,plain,(
    ! [A_154] : v1_relat_1(k7_relat_1('#skF_4',A_154)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_364])).

tff(c_20,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(k7_relat_1(B_35,A_34)) = k9_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k2_relat_1(A_75),k2_relat_1(B_76))
      | ~ r1_tarski(A_75,B_76)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_426,plain,(
    ! [B_183,A_184,B_185] :
      ( r1_tarski(k9_relat_1(B_183,A_184),k2_relat_1(B_185))
      | ~ r1_tarski(k7_relat_1(B_183,A_184),B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(k7_relat_1(B_183,A_184))
      | ~ v1_relat_1(B_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_111])).

tff(c_261,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_431,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_426,c_261])).

tff(c_438,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_368,c_431])).

tff(c_441,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_438])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:15:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.69  
% 2.76/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.69  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.76/1.69  
% 2.76/1.69  %Foreground sorts:
% 2.76/1.69  
% 2.76/1.69  
% 2.76/1.69  %Background operators:
% 2.76/1.69  
% 2.76/1.69  
% 2.76/1.69  %Foreground operators:
% 2.76/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.69  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.76/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.69  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.76/1.69  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.69  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.76/1.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.69  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.69  
% 2.76/1.71  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.76/1.71  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.76/1.71  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.76/1.71  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.76/1.71  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.76/1.71  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.76/1.71  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.76/1.71  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.76/1.71  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 2.76/1.71  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.76/1.71  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.76/1.71  tff(c_18, plain, (![A_32, B_33]: (v1_relat_1(k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.71  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.76/1.71  tff(c_77, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.71  tff(c_80, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_77])).
% 2.76/1.71  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_80])).
% 2.76/1.71  tff(c_26, plain, (![B_40, A_39]: (r1_tarski(k7_relat_1(B_40, A_39), B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.71  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.76/1.71  tff(c_153, plain, (![B_95, A_96]: (k1_tarski(k1_funct_1(B_95, A_96))=k2_relat_1(B_95) | k1_tarski(A_96)!=k1_relat_1(B_95) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.76/1.71  tff(c_138, plain, (![A_88, B_89, C_90, D_91]: (k7_relset_1(A_88, B_89, C_90, D_91)=k9_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.71  tff(c_141, plain, (![D_91]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_91)=k9_relat_1('#skF_4', D_91))), inference(resolution, [status(thm)], [c_52, c_138])).
% 2.76/1.71  tff(c_48, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.76/1.71  tff(c_142, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_48])).
% 2.76/1.71  tff(c_159, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_153, c_142])).
% 2.76/1.71  tff(c_165, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_159])).
% 2.76/1.71  tff(c_168, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_165])).
% 2.76/1.71  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.76/1.71  tff(c_54, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.76/1.71  tff(c_118, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.71  tff(c_122, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_118])).
% 2.76/1.71  tff(c_248, plain, (![B_130, A_131, C_132]: (k1_xboole_0=B_130 | k1_relset_1(A_131, B_130, C_132)=A_131 | ~v1_funct_2(C_132, A_131, B_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.76/1.71  tff(c_254, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_52, c_248])).
% 2.76/1.71  tff(c_258, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_122, c_254])).
% 2.76/1.71  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_50, c_258])).
% 2.76/1.71  tff(c_262, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_165])).
% 2.76/1.71  tff(c_265, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_52])).
% 2.76/1.71  tff(c_309, plain, (![A_142, B_143, C_144, D_145]: (m1_subset_1(A_142, k1_zfmisc_1(k2_zfmisc_1(B_143, C_144))) | ~r1_tarski(A_142, D_145) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(B_143, C_144))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.76/1.71  tff(c_319, plain, (![B_146, A_147, B_148, C_149]: (m1_subset_1(k7_relat_1(B_146, A_147), k1_zfmisc_1(k2_zfmisc_1(B_148, C_149))) | ~m1_subset_1(B_146, k1_zfmisc_1(k2_zfmisc_1(B_148, C_149))) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_26, c_309])).
% 2.76/1.71  tff(c_16, plain, (![B_31, A_29]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.71  tff(c_339, plain, (![B_146, A_147, B_148, C_149]: (v1_relat_1(k7_relat_1(B_146, A_147)) | ~v1_relat_1(k2_zfmisc_1(B_148, C_149)) | ~m1_subset_1(B_146, k1_zfmisc_1(k2_zfmisc_1(B_148, C_149))) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_319, c_16])).
% 2.76/1.71  tff(c_360, plain, (![B_153, A_154, B_155, C_156]: (v1_relat_1(k7_relat_1(B_153, A_154)) | ~m1_subset_1(B_153, k1_zfmisc_1(k2_zfmisc_1(B_155, C_156))) | ~v1_relat_1(B_153))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_339])).
% 2.76/1.71  tff(c_364, plain, (![A_154]: (v1_relat_1(k7_relat_1('#skF_4', A_154)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_265, c_360])).
% 2.76/1.71  tff(c_368, plain, (![A_154]: (v1_relat_1(k7_relat_1('#skF_4', A_154)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_364])).
% 2.76/1.71  tff(c_20, plain, (![B_35, A_34]: (k2_relat_1(k7_relat_1(B_35, A_34))=k9_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.76/1.71  tff(c_111, plain, (![A_75, B_76]: (r1_tarski(k2_relat_1(A_75), k2_relat_1(B_76)) | ~r1_tarski(A_75, B_76) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.76/1.71  tff(c_426, plain, (![B_183, A_184, B_185]: (r1_tarski(k9_relat_1(B_183, A_184), k2_relat_1(B_185)) | ~r1_tarski(k7_relat_1(B_183, A_184), B_185) | ~v1_relat_1(B_185) | ~v1_relat_1(k7_relat_1(B_183, A_184)) | ~v1_relat_1(B_183))), inference(superposition, [status(thm), theory('equality')], [c_20, c_111])).
% 2.76/1.71  tff(c_261, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_165])).
% 2.76/1.71  tff(c_431, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_426, c_261])).
% 2.76/1.71  tff(c_438, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_368, c_431])).
% 2.76/1.71  tff(c_441, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_438])).
% 2.76/1.71  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_441])).
% 2.76/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.71  
% 2.76/1.71  Inference rules
% 2.76/1.71  ----------------------
% 2.76/1.71  #Ref     : 0
% 2.76/1.71  #Sup     : 83
% 2.76/1.71  #Fact    : 0
% 2.76/1.71  #Define  : 0
% 2.76/1.71  #Split   : 1
% 2.76/1.71  #Chain   : 0
% 2.76/1.71  #Close   : 0
% 2.76/1.71  
% 2.76/1.71  Ordering : KBO
% 2.76/1.71  
% 2.76/1.71  Simplification rules
% 2.76/1.71  ----------------------
% 2.76/1.71  #Subsume      : 1
% 2.76/1.71  #Demod        : 30
% 2.76/1.71  #Tautology    : 39
% 2.76/1.71  #SimpNegUnit  : 4
% 2.76/1.71  #BackRed      : 5
% 2.76/1.71  
% 2.76/1.71  #Partial instantiations: 0
% 2.76/1.71  #Strategies tried      : 1
% 2.76/1.71  
% 2.76/1.71  Timing (in seconds)
% 2.76/1.71  ----------------------
% 2.76/1.71  Preprocessing        : 0.55
% 2.76/1.71  Parsing              : 0.37
% 2.76/1.71  CNF conversion       : 0.02
% 2.76/1.71  Main loop            : 0.26
% 2.76/1.71  Inferencing          : 0.10
% 2.76/1.71  Reduction            : 0.08
% 2.76/1.71  Demodulation         : 0.05
% 2.76/1.71  BG Simplification    : 0.02
% 2.76/1.71  Subsumption          : 0.04
% 2.76/1.71  Abstraction          : 0.01
% 2.76/1.71  MUC search           : 0.00
% 2.76/1.71  Cooper               : 0.00
% 2.76/1.71  Total                : 0.84
% 2.76/1.71  Index Insertion      : 0.00
% 2.76/1.71  Index Deletion       : 0.00
% 2.76/1.71  Index Matching       : 0.00
% 2.76/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
