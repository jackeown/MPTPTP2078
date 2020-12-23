%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:08 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 258 expanded)
%              Number of leaves         :   35 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 480 expanded)
%              Number of equality atoms :   32 (  96 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_46,plain,
    ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_28,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_62,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_59])).

tff(c_93,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_98,plain,(
    ! [B_77,A_78] :
      ( k7_relat_1(B_77,A_78) = B_77
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,
    ( k7_relat_1('#skF_8','#skF_7') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_97,c_98])).

tff(c_104,plain,(
    k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_101])).

tff(c_32,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_35,A_34)),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_112,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_32])).

tff(c_116,plain,(
    r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_112])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_120,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_116,c_8])).

tff(c_125,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_130,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_126])).

tff(c_131,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_64])).

tff(c_52,plain,(
    ! [D_48] :
      ( r2_hidden(k4_tarski(D_48,'#skF_9'(D_48)),'#skF_8')
      | ~ r2_hidden(D_48,'#skF_7')
      | k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_136,plain,(
    ! [D_48] :
      ( r2_hidden(k4_tarski(D_48,'#skF_9'(D_48)),'#skF_8')
      | ~ r2_hidden(D_48,'#skF_7')
      | k1_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_52])).

tff(c_138,plain,(
    ! [D_83] :
      ( r2_hidden(k4_tarski(D_83,'#skF_9'(D_83)),'#skF_8')
      | ~ r2_hidden(D_83,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_136])).

tff(c_18,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k1_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(C_26,D_29),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    ! [D_84] :
      ( r2_hidden(D_84,k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_84,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_138,c_18])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_91,k1_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_184,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_125,c_184])).

tff(c_189,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_191,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_195,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_191])).

tff(c_203,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_195])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_203])).

tff(c_205,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_206,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_295,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_298,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_295])).

tff(c_300,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_298])).

tff(c_241,plain,(
    ! [C_102,A_103,B_104] :
      ( v4_relat_1(C_102,A_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_245,plain,(
    v4_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_241])).

tff(c_263,plain,(
    ! [B_115,A_116] :
      ( k7_relat_1(B_115,A_116) = B_115
      | ~ v4_relat_1(B_115,A_116)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_266,plain,
    ( k7_relat_1('#skF_8','#skF_7') = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_245,c_263])).

tff(c_269,plain,(
    k7_relat_1('#skF_8','#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_266])).

tff(c_274,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_32])).

tff(c_278,plain,(
    r1_tarski(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_274])).

tff(c_282,plain,
    ( k1_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_278,c_8])).

tff(c_283,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_301,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_283])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_301])).

tff(c_306,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_344,plain,(
    ! [C_134,A_135] :
      ( r2_hidden(k4_tarski(C_134,'#skF_5'(A_135,k1_relat_1(A_135),C_134)),A_135)
      | ~ r2_hidden(C_134,k1_relat_1(A_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [E_51] :
      ( k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski('#skF_10',E_51),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_207,plain,(
    k1_relset_1('#skF_7','#skF_6','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_207])).

tff(c_214,plain,(
    ! [E_51] : ~ r2_hidden(k4_tarski('#skF_10',E_51),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_353,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_344,c_214])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_306,c_353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:37:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.37/1.34  
% 2.37/1.34  %Foreground sorts:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Background operators:
% 2.37/1.34  
% 2.37/1.34  
% 2.37/1.34  %Foreground operators:
% 2.37/1.34  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.37/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.37/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.37/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.34  tff('#skF_10', type, '#skF_10': $i).
% 2.37/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.37/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.37/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.37/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.37/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.34  
% 2.37/1.36  tff(f_88, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 2.37/1.36  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.37/1.36  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.37/1.36  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.37/1.36  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.37/1.36  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.37/1.36  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.37/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.37/1.36  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.37/1.36  tff(f_53, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.37/1.36  tff(c_46, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.37/1.36  tff(c_64, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_46])).
% 2.37/1.36  tff(c_28, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.36  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.37/1.36  tff(c_56, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.37/1.36  tff(c_59, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.37/1.36  tff(c_62, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_59])).
% 2.37/1.36  tff(c_93, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.36  tff(c_97, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_93])).
% 2.37/1.36  tff(c_98, plain, (![B_77, A_78]: (k7_relat_1(B_77, A_78)=B_77 | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.36  tff(c_101, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_97, c_98])).
% 2.37/1.36  tff(c_104, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_101])).
% 2.37/1.36  tff(c_32, plain, (![B_35, A_34]: (r1_tarski(k1_relat_1(k7_relat_1(B_35, A_34)), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.37/1.36  tff(c_112, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_104, c_32])).
% 2.37/1.36  tff(c_116, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_112])).
% 2.37/1.36  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.36  tff(c_120, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_116, c_8])).
% 2.37/1.36  tff(c_125, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_120])).
% 2.37/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.36  tff(c_126, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.37/1.36  tff(c_130, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_126])).
% 2.37/1.36  tff(c_131, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_64])).
% 2.37/1.36  tff(c_52, plain, (![D_48]: (r2_hidden(k4_tarski(D_48, '#skF_9'(D_48)), '#skF_8') | ~r2_hidden(D_48, '#skF_7') | k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.37/1.36  tff(c_136, plain, (![D_48]: (r2_hidden(k4_tarski(D_48, '#skF_9'(D_48)), '#skF_8') | ~r2_hidden(D_48, '#skF_7') | k1_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_52])).
% 2.37/1.36  tff(c_138, plain, (![D_83]: (r2_hidden(k4_tarski(D_83, '#skF_9'(D_83)), '#skF_8') | ~r2_hidden(D_83, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_131, c_136])).
% 2.37/1.36  tff(c_18, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k1_relat_1(A_11)) | ~r2_hidden(k4_tarski(C_26, D_29), A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.36  tff(c_146, plain, (![D_84]: (r2_hidden(D_84, k1_relat_1('#skF_8')) | ~r2_hidden(D_84, '#skF_7'))), inference(resolution, [status(thm)], [c_138, c_18])).
% 2.37/1.36  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.36  tff(c_180, plain, (![A_91]: (r1_tarski(A_91, k1_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_91, k1_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_146, c_4])).
% 2.37/1.36  tff(c_184, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_180])).
% 2.37/1.36  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_125, c_184])).
% 2.37/1.36  tff(c_189, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_120])).
% 2.37/1.36  tff(c_191, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.37/1.36  tff(c_195, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_191])).
% 2.37/1.36  tff(c_203, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_195])).
% 2.37/1.36  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_203])).
% 2.37/1.36  tff(c_205, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 2.37/1.36  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.36  tff(c_206, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_46])).
% 2.37/1.36  tff(c_295, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.37/1.36  tff(c_298, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_295])).
% 2.37/1.36  tff(c_300, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_298])).
% 2.37/1.36  tff(c_241, plain, (![C_102, A_103, B_104]: (v4_relat_1(C_102, A_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.36  tff(c_245, plain, (v4_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_241])).
% 2.37/1.36  tff(c_263, plain, (![B_115, A_116]: (k7_relat_1(B_115, A_116)=B_115 | ~v4_relat_1(B_115, A_116) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.36  tff(c_266, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_245, c_263])).
% 2.37/1.36  tff(c_269, plain, (k7_relat_1('#skF_8', '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_266])).
% 2.37/1.36  tff(c_274, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_269, c_32])).
% 2.37/1.36  tff(c_278, plain, (r1_tarski(k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_274])).
% 2.37/1.36  tff(c_282, plain, (k1_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_278, c_8])).
% 2.37/1.36  tff(c_283, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_282])).
% 2.37/1.36  tff(c_301, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_283])).
% 2.37/1.36  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_301])).
% 2.37/1.36  tff(c_306, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_282])).
% 2.37/1.36  tff(c_344, plain, (![C_134, A_135]: (r2_hidden(k4_tarski(C_134, '#skF_5'(A_135, k1_relat_1(A_135), C_134)), A_135) | ~r2_hidden(C_134, k1_relat_1(A_135)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.36  tff(c_42, plain, (![E_51]: (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski('#skF_10', E_51), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.37/1.36  tff(c_207, plain, (k1_relset_1('#skF_7', '#skF_6', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_42])).
% 2.37/1.36  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_207])).
% 2.37/1.36  tff(c_214, plain, (![E_51]: (~r2_hidden(k4_tarski('#skF_10', E_51), '#skF_8'))), inference(splitRight, [status(thm)], [c_42])).
% 2.37/1.36  tff(c_353, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_344, c_214])).
% 2.37/1.36  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_306, c_353])).
% 2.37/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.36  
% 2.37/1.36  Inference rules
% 2.37/1.36  ----------------------
% 2.37/1.36  #Ref     : 0
% 2.37/1.36  #Sup     : 64
% 2.37/1.36  #Fact    : 0
% 2.37/1.36  #Define  : 0
% 2.37/1.36  #Split   : 5
% 2.37/1.36  #Chain   : 0
% 2.37/1.36  #Close   : 0
% 2.37/1.36  
% 2.37/1.36  Ordering : KBO
% 2.37/1.36  
% 2.37/1.36  Simplification rules
% 2.37/1.36  ----------------------
% 2.37/1.36  #Subsume      : 8
% 2.37/1.36  #Demod        : 39
% 2.37/1.36  #Tautology    : 32
% 2.37/1.36  #SimpNegUnit  : 3
% 2.37/1.36  #BackRed      : 5
% 2.37/1.36  
% 2.37/1.36  #Partial instantiations: 0
% 2.37/1.36  #Strategies tried      : 1
% 2.37/1.36  
% 2.37/1.36  Timing (in seconds)
% 2.37/1.36  ----------------------
% 2.37/1.36  Preprocessing        : 0.33
% 2.37/1.36  Parsing              : 0.17
% 2.37/1.36  CNF conversion       : 0.02
% 2.37/1.36  Main loop            : 0.23
% 2.37/1.36  Inferencing          : 0.08
% 2.37/1.36  Reduction            : 0.07
% 2.37/1.36  Demodulation         : 0.05
% 2.37/1.36  BG Simplification    : 0.01
% 2.37/1.36  Subsumption          : 0.04
% 2.37/1.36  Abstraction          : 0.01
% 2.37/1.36  MUC search           : 0.00
% 2.37/1.36  Cooper               : 0.00
% 2.37/1.36  Total                : 0.60
% 2.37/1.36  Index Insertion      : 0.00
% 2.37/1.36  Index Deletion       : 0.00
% 2.37/1.36  Index Matching       : 0.00
% 2.37/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
