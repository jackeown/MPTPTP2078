%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:08 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 224 expanded)
%              Number of leaves         :   34 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 412 expanded)
%              Number of equality atoms :   30 (  93 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_44,plain,
    ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_69,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_79,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_83,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_26,plain,(
    ! [B_28,A_27] :
      ( k7_relat_1(B_28,A_27) = B_28
      | ~ v4_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,
    ( k7_relat_1('#skF_8','#skF_7') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_83,c_26])).

tff(c_89,plain,(
    k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_86])).

tff(c_28,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_30,A_29)),A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_28])).

tff(c_97,plain,(
    r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_93])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_97,c_8])).

tff(c_103,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_121])).

tff(c_126,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_69])).

tff(c_50,plain,(
    ! [D_46] :
      ( r2_hidden(k4_tarski(D_46,'#skF_9'(D_46)),'#skF_8')
      | ~ r2_hidden(D_46,'#skF_7')
      | k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_142,plain,(
    ! [D_46] :
      ( r2_hidden(k4_tarski(D_46,'#skF_9'(D_46)),'#skF_8')
      | ~ r2_hidden(D_46,'#skF_7')
      | k1_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_50])).

tff(c_144,plain,(
    ! [D_82] :
      ( r2_hidden(k4_tarski(D_82,'#skF_9'(D_82)),'#skF_8')
      | ~ r2_hidden(D_82,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_142])).

tff(c_16,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [D_83] :
      ( r2_hidden(D_83,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_83,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_144,c_16])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_88,k1_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_152,c_4])).

tff(c_179,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_103,c_179])).

tff(c_184,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_232,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_235,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_232])).

tff(c_237,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_235])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_237])).

tff(c_240,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_241,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_311,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_314,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_311])).

tff(c_316,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_314])).

tff(c_258,plain,(
    ! [C_113,A_114,B_115] :
      ( v4_relat_1(C_113,A_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_262,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_258])).

tff(c_265,plain,
    ( k7_relat_1('#skF_8','#skF_7') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_262,c_26])).

tff(c_268,plain,(
    k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_265])).

tff(c_272,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_28])).

tff(c_276,plain,(
    r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_272])).

tff(c_281,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_276,c_8])).

tff(c_282,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_317,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_282])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_317])).

tff(c_322,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_376,plain,(
    ! [C_148,A_149] :
      ( r2_hidden(k4_tarski(C_148,'#skF_5'(A_149,k1_relat_1(A_149),C_148)),A_149)
      | ~ r2_hidden(C_148,k1_relat_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [E_49] :
      ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski('#skF_10',E_49),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_248,plain,(
    ! [E_49] : ~ r2_hidden(k4_tarski('#skF_10',E_49),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_40])).

tff(c_385,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_376,c_248])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_322,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.17/1.30  
% 2.17/1.30  %Foreground sorts:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Background operators:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Foreground operators:
% 2.17/1.30  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.17/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.30  tff('#skF_10', type, '#skF_10': $i).
% 2.17/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.17/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.17/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.30  
% 2.17/1.31  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 2.17/1.31  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.17/1.31  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.17/1.31  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.17/1.31  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.17/1.31  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.17/1.31  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.17/1.31  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.17/1.31  tff(c_44, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.17/1.31  tff(c_69, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 2.17/1.31  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.17/1.31  tff(c_53, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.31  tff(c_57, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_53])).
% 2.17/1.31  tff(c_79, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.31  tff(c_83, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.17/1.31  tff(c_26, plain, (![B_28, A_27]: (k7_relat_1(B_28, A_27)=B_28 | ~v4_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.31  tff(c_86, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_83, c_26])).
% 2.17/1.31  tff(c_89, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_86])).
% 2.17/1.31  tff(c_28, plain, (![B_30, A_29]: (r1_tarski(k1_relat_1(k7_relat_1(B_30, A_29)), A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.31  tff(c_93, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_89, c_28])).
% 2.17/1.31  tff(c_97, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_93])).
% 2.17/1.31  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.31  tff(c_102, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_97, c_8])).
% 2.17/1.31  tff(c_103, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_102])).
% 2.17/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.31  tff(c_121, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.31  tff(c_125, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_121])).
% 2.17/1.31  tff(c_126, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_69])).
% 2.17/1.31  tff(c_50, plain, (![D_46]: (r2_hidden(k4_tarski(D_46, '#skF_9'(D_46)), '#skF_8') | ~r2_hidden(D_46, '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.17/1.31  tff(c_142, plain, (![D_46]: (r2_hidden(k4_tarski(D_46, '#skF_9'(D_46)), '#skF_8') | ~r2_hidden(D_46, '#skF_7') | k1_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_50])).
% 2.17/1.31  tff(c_144, plain, (![D_82]: (r2_hidden(k4_tarski(D_82, '#skF_9'(D_82)), '#skF_8') | ~r2_hidden(D_82, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_126, c_142])).
% 2.17/1.31  tff(c_16, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k1_relat_1(A_8)) | ~r2_hidden(k4_tarski(C_23, D_26), A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.31  tff(c_152, plain, (![D_83]: (r2_hidden(D_83, k1_relat_1('#skF_8')) | ~r2_hidden(D_83, '#skF_7'))), inference(resolution, [status(thm)], [c_144, c_16])).
% 2.17/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.31  tff(c_175, plain, (![A_88]: (r1_tarski(A_88, k1_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_88, k1_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_152, c_4])).
% 2.17/1.31  tff(c_179, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_175])).
% 2.17/1.31  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_103, c_179])).
% 2.17/1.31  tff(c_184, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_102])).
% 2.17/1.31  tff(c_232, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.31  tff(c_235, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_232])).
% 2.17/1.31  tff(c_237, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_235])).
% 2.17/1.31  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_237])).
% 2.17/1.31  tff(c_240, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 2.17/1.31  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.31  tff(c_241, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 2.17/1.31  tff(c_311, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.31  tff(c_314, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_311])).
% 2.17/1.31  tff(c_316, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_314])).
% 2.17/1.31  tff(c_258, plain, (![C_113, A_114, B_115]: (v4_relat_1(C_113, A_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.31  tff(c_262, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_258])).
% 2.17/1.31  tff(c_265, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_262, c_26])).
% 2.17/1.31  tff(c_268, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_265])).
% 2.17/1.31  tff(c_272, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_268, c_28])).
% 2.17/1.31  tff(c_276, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_272])).
% 2.17/1.31  tff(c_281, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_276, c_8])).
% 2.17/1.31  tff(c_282, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_281])).
% 2.17/1.31  tff(c_317, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_282])).
% 2.17/1.31  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_317])).
% 2.17/1.31  tff(c_322, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_281])).
% 2.17/1.31  tff(c_376, plain, (![C_148, A_149]: (r2_hidden(k4_tarski(C_148, '#skF_5'(A_149, k1_relat_1(A_149), C_148)), A_149) | ~r2_hidden(C_148, k1_relat_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.31  tff(c_40, plain, (![E_49]: (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski('#skF_10', E_49), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.17/1.31  tff(c_248, plain, (![E_49]: (~r2_hidden(k4_tarski('#skF_10', E_49), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_40])).
% 2.17/1.31  tff(c_385, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_376, c_248])).
% 2.17/1.31  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_322, c_385])).
% 2.17/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  Inference rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Ref     : 0
% 2.17/1.31  #Sup     : 73
% 2.17/1.31  #Fact    : 0
% 2.17/1.31  #Define  : 0
% 2.17/1.31  #Split   : 5
% 2.17/1.31  #Chain   : 0
% 2.17/1.31  #Close   : 0
% 2.17/1.31  
% 2.17/1.31  Ordering : KBO
% 2.17/1.31  
% 2.17/1.31  Simplification rules
% 2.17/1.31  ----------------------
% 2.17/1.31  #Subsume      : 8
% 2.17/1.31  #Demod        : 40
% 2.17/1.31  #Tautology    : 30
% 2.17/1.31  #SimpNegUnit  : 3
% 2.17/1.31  #BackRed      : 5
% 2.17/1.31  
% 2.17/1.31  #Partial instantiations: 0
% 2.17/1.31  #Strategies tried      : 1
% 2.17/1.31  
% 2.17/1.31  Timing (in seconds)
% 2.17/1.31  ----------------------
% 2.17/1.32  Preprocessing        : 0.31
% 2.17/1.32  Parsing              : 0.16
% 2.17/1.32  CNF conversion       : 0.02
% 2.17/1.32  Main loop            : 0.23
% 2.17/1.32  Inferencing          : 0.08
% 2.17/1.32  Reduction            : 0.07
% 2.17/1.32  Demodulation         : 0.05
% 2.17/1.32  BG Simplification    : 0.01
% 2.17/1.32  Subsumption          : 0.05
% 2.17/1.32  Abstraction          : 0.01
% 2.17/1.32  MUC search           : 0.00
% 2.17/1.32  Cooper               : 0.00
% 2.17/1.32  Total                : 0.58
% 2.17/1.32  Index Insertion      : 0.00
% 2.17/1.32  Index Deletion       : 0.00
% 2.17/1.32  Index Matching       : 0.00
% 2.17/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
