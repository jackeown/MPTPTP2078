%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:11 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.61s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 218 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 454 expanded)
%              Number of equality atoms :   26 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_38,plain,
    ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_9'(D_40),D_40),'#skF_8')
      | ~ r2_hidden(D_40,'#skF_7')
      | k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [D_73] :
      ( r2_hidden(k4_tarski('#skF_9'(D_73),D_73),'#skF_8')
      | ~ r2_hidden(D_73,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_44])).

tff(c_20,plain,(
    ! [C_27,A_12,D_30] :
      ( r2_hidden(C_27,k2_relat_1(A_12))
      | ~ r2_hidden(k4_tarski(D_30,C_27),A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,(
    ! [D_74] :
      ( r2_hidden(D_74,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_74,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_96,c_20])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_75,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_129,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_135,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_144,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_148,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_63])).

tff(c_967,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(k4_tarski('#skF_3'(A_165,B_166),'#skF_2'(A_165,B_166)),A_165)
      | r2_hidden('#skF_4'(A_165,B_166),B_166)
      | k2_relat_1(A_165) = B_166 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1006,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_2'(A_165,B_166),k2_relat_1(A_165))
      | r2_hidden('#skF_4'(A_165,B_166),B_166)
      | k2_relat_1(A_165) = B_166 ) ),
    inference(resolution,[status(thm)],[c_967,c_20])).

tff(c_46,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_497,plain,(
    ! [A_129,C_130] :
      ( r2_hidden(k4_tarski('#skF_5'(A_129,k2_relat_1(A_129),C_130),C_130),A_129)
      | ~ r2_hidden(C_130,k2_relat_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1881,plain,(
    ! [A_217,C_218,B_219] :
      ( r2_hidden(k4_tarski('#skF_5'(A_217,k2_relat_1(A_217),C_218),C_218),B_219)
      | ~ r1_tarski(A_217,B_219)
      | ~ r2_hidden(C_218,k2_relat_1(A_217)) ) ),
    inference(resolution,[status(thm)],[c_497,c_2])).

tff(c_1940,plain,(
    ! [C_220,B_221,A_222] :
      ( r2_hidden(C_220,k2_relat_1(B_221))
      | ~ r1_tarski(A_222,B_221)
      | ~ r2_hidden(C_220,k2_relat_1(A_222)) ) ),
    inference(resolution,[status(thm)],[c_1881,c_20])).

tff(c_1971,plain,(
    ! [C_223] :
      ( r2_hidden(C_223,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ r2_hidden(C_223,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_54,c_1940])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_522,plain,(
    ! [C_130,D_9,C_8] :
      ( r2_hidden(C_130,D_9)
      | ~ r2_hidden(C_130,k2_relat_1(k2_zfmisc_1(C_8,D_9))) ) ),
    inference(resolution,[status(thm)],[c_497,c_10])).

tff(c_2020,plain,(
    ! [C_224] :
      ( r2_hidden(C_224,'#skF_7')
      | ~ r2_hidden(C_224,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1971,c_522])).

tff(c_3346,plain,(
    ! [B_274] :
      ( r2_hidden('#skF_2'('#skF_8',B_274),'#skF_7')
      | r2_hidden('#skF_4'('#skF_8',B_274),B_274)
      | k2_relat_1('#skF_8') = B_274 ) ),
    inference(resolution,[status(thm)],[c_1006,c_2020])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_2'(A_12,B_13),B_13)
      | r2_hidden('#skF_4'(A_12,B_13),B_13)
      | k2_relat_1(A_12) = B_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3359,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3346,c_26])).

tff(c_3396,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_148,c_3359])).

tff(c_3420,plain,(
    ! [B_275] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_275)
      | ~ r1_tarski('#skF_7',B_275) ) ),
    inference(resolution,[status(thm)],[c_3396,c_2])).

tff(c_3562,plain,(
    ! [B_283,B_284] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),B_283)
      | ~ r1_tarski(B_284,B_283)
      | ~ r1_tarski('#skF_7',B_284) ) ),
    inference(resolution,[status(thm)],[c_3420,c_2])).

tff(c_3582,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_129,c_3562])).

tff(c_3604,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_3582])).

tff(c_18,plain,(
    ! [A_12,C_27] :
      ( r2_hidden(k4_tarski('#skF_5'(A_12,k2_relat_1(A_12),C_27),C_27),A_12)
      | ~ r2_hidden(C_27,k2_relat_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_9'(D_40),D_40),'#skF_8')
      | ~ r2_hidden(D_40,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_44])).

tff(c_1424,plain,(
    ! [A_191,B_192,D_193] :
      ( r2_hidden(k4_tarski('#skF_3'(A_191,B_192),'#skF_2'(A_191,B_192)),A_191)
      | ~ r2_hidden(k4_tarski(D_193,'#skF_4'(A_191,B_192)),A_191)
      | k2_relat_1(A_191) = B_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1553,plain,(
    ! [B_198] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_8',B_198),'#skF_2'('#skF_8',B_198)),'#skF_8')
      | k2_relat_1('#skF_8') = B_198
      | ~ r2_hidden('#skF_4'('#skF_8',B_198),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_95,c_1424])).

tff(c_5534,plain,(
    ! [B_355] :
      ( r2_hidden('#skF_2'('#skF_8',B_355),k2_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_355
      | ~ r2_hidden('#skF_4'('#skF_8',B_355),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1553,c_20])).

tff(c_2013,plain,(
    ! [C_223] :
      ( r2_hidden(C_223,'#skF_7')
      | ~ r2_hidden(C_223,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1971,c_522])).

tff(c_6981,plain,(
    ! [B_405] :
      ( r2_hidden('#skF_2'('#skF_8',B_405),'#skF_7')
      | k2_relat_1('#skF_8') = B_405
      | ~ r2_hidden('#skF_4'('#skF_8',B_405),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5534,c_2013])).

tff(c_22,plain,(
    ! [A_12,B_13,D_26] :
      ( ~ r2_hidden('#skF_2'(A_12,B_13),B_13)
      | ~ r2_hidden(k4_tarski(D_26,'#skF_4'(A_12,B_13)),A_12)
      | k2_relat_1(A_12) = B_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6990,plain,(
    ! [D_26] :
      ( ~ r2_hidden(k4_tarski(D_26,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6981,c_22])).

tff(c_7008,plain,(
    ! [D_26] :
      ( ~ r2_hidden(k4_tarski(D_26,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_6990])).

tff(c_7016,plain,(
    ! [D_406] : ~ r2_hidden(k4_tarski(D_406,'#skF_4'('#skF_8','#skF_7')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_7008])).

tff(c_7024,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_18,c_7016])).

tff(c_7037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3604,c_7024])).

tff(c_7038,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_7039,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_7078,plain,(
    ! [A_428,B_429,C_430] :
      ( k2_relset_1(A_428,B_429,C_430) = k2_relat_1(C_430)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(A_428,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7085,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_7078])).

tff(c_7088,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7039,c_7085])).

tff(c_7115,plain,(
    ! [A_438,C_439] :
      ( r2_hidden(k4_tarski('#skF_5'(A_438,k2_relat_1(A_438),C_439),C_439),A_438)
      | ~ r2_hidden(C_439,k2_relat_1(A_438)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [E_43] :
      ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski(E_43,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7064,plain,(
    ! [E_43] : ~ r2_hidden(k4_tarski(E_43,'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7039,c_34])).

tff(c_7127,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_7115,c_7064])).

tff(c_7141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7038,c_7088,c_7127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.28/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.84  
% 8.28/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/2.84  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 8.61/2.84  
% 8.61/2.84  %Foreground sorts:
% 8.61/2.84  
% 8.61/2.84  
% 8.61/2.84  %Background operators:
% 8.61/2.84  
% 8.61/2.84  
% 8.61/2.84  %Foreground operators:
% 8.61/2.84  tff('#skF_9', type, '#skF_9': $i > $i).
% 8.61/2.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.61/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.61/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.61/2.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.61/2.84  tff('#skF_7', type, '#skF_7': $i).
% 8.61/2.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.61/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.61/2.84  tff('#skF_10', type, '#skF_10': $i).
% 8.61/2.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.61/2.84  tff('#skF_6', type, '#skF_6': $i).
% 8.61/2.84  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.61/2.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.61/2.84  tff('#skF_8', type, '#skF_8': $i).
% 8.61/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.61/2.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.61/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.61/2.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.61/2.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.61/2.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.61/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.61/2.84  
% 8.61/2.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.61/2.85  tff(f_67, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 8.61/2.85  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.61/2.85  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.61/2.85  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.61/2.85  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.61/2.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.61/2.85  tff(c_56, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.61/2.85  tff(c_61, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_56])).
% 8.61/2.85  tff(c_38, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.61/2.85  tff(c_63, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_38])).
% 8.61/2.85  tff(c_44, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_9'(D_40), D_40), '#skF_8') | ~r2_hidden(D_40, '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.61/2.85  tff(c_96, plain, (![D_73]: (r2_hidden(k4_tarski('#skF_9'(D_73), D_73), '#skF_8') | ~r2_hidden(D_73, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_63, c_44])).
% 8.61/2.85  tff(c_20, plain, (![C_27, A_12, D_30]: (r2_hidden(C_27, k2_relat_1(A_12)) | ~r2_hidden(k4_tarski(D_30, C_27), A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_104, plain, (![D_74]: (r2_hidden(D_74, k2_relat_1('#skF_8')) | ~r2_hidden(D_74, '#skF_7'))), inference(resolution, [status(thm)], [c_96, c_20])).
% 8.61/2.85  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.61/2.85  tff(c_119, plain, (![A_75]: (r1_tarski(A_75, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_75, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_104, c_4])).
% 8.61/2.85  tff(c_129, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_119])).
% 8.61/2.85  tff(c_32, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.61/2.85  tff(c_135, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.61/2.85  tff(c_144, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_135])).
% 8.61/2.85  tff(c_148, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_63])).
% 8.61/2.85  tff(c_967, plain, (![A_165, B_166]: (r2_hidden(k4_tarski('#skF_3'(A_165, B_166), '#skF_2'(A_165, B_166)), A_165) | r2_hidden('#skF_4'(A_165, B_166), B_166) | k2_relat_1(A_165)=B_166)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_1006, plain, (![A_165, B_166]: (r2_hidden('#skF_2'(A_165, B_166), k2_relat_1(A_165)) | r2_hidden('#skF_4'(A_165, B_166), B_166) | k2_relat_1(A_165)=B_166)), inference(resolution, [status(thm)], [c_967, c_20])).
% 8.61/2.85  tff(c_46, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.61/2.85  tff(c_54, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_46])).
% 8.61/2.85  tff(c_497, plain, (![A_129, C_130]: (r2_hidden(k4_tarski('#skF_5'(A_129, k2_relat_1(A_129), C_130), C_130), A_129) | ~r2_hidden(C_130, k2_relat_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.61/2.85  tff(c_1881, plain, (![A_217, C_218, B_219]: (r2_hidden(k4_tarski('#skF_5'(A_217, k2_relat_1(A_217), C_218), C_218), B_219) | ~r1_tarski(A_217, B_219) | ~r2_hidden(C_218, k2_relat_1(A_217)))), inference(resolution, [status(thm)], [c_497, c_2])).
% 8.61/2.85  tff(c_1940, plain, (![C_220, B_221, A_222]: (r2_hidden(C_220, k2_relat_1(B_221)) | ~r1_tarski(A_222, B_221) | ~r2_hidden(C_220, k2_relat_1(A_222)))), inference(resolution, [status(thm)], [c_1881, c_20])).
% 8.61/2.85  tff(c_1971, plain, (![C_223]: (r2_hidden(C_223, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~r2_hidden(C_223, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_54, c_1940])).
% 8.61/2.85  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.61/2.85  tff(c_522, plain, (![C_130, D_9, C_8]: (r2_hidden(C_130, D_9) | ~r2_hidden(C_130, k2_relat_1(k2_zfmisc_1(C_8, D_9))))), inference(resolution, [status(thm)], [c_497, c_10])).
% 8.61/2.85  tff(c_2020, plain, (![C_224]: (r2_hidden(C_224, '#skF_7') | ~r2_hidden(C_224, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1971, c_522])).
% 8.61/2.85  tff(c_3346, plain, (![B_274]: (r2_hidden('#skF_2'('#skF_8', B_274), '#skF_7') | r2_hidden('#skF_4'('#skF_8', B_274), B_274) | k2_relat_1('#skF_8')=B_274)), inference(resolution, [status(thm)], [c_1006, c_2020])).
% 8.61/2.85  tff(c_26, plain, (![A_12, B_13]: (~r2_hidden('#skF_2'(A_12, B_13), B_13) | r2_hidden('#skF_4'(A_12, B_13), B_13) | k2_relat_1(A_12)=B_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_3359, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_3346, c_26])).
% 8.61/2.85  tff(c_3396, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_148, c_148, c_3359])).
% 8.61/2.85  tff(c_3420, plain, (![B_275]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_275) | ~r1_tarski('#skF_7', B_275))), inference(resolution, [status(thm)], [c_3396, c_2])).
% 8.61/2.85  tff(c_3562, plain, (![B_283, B_284]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_283) | ~r1_tarski(B_284, B_283) | ~r1_tarski('#skF_7', B_284))), inference(resolution, [status(thm)], [c_3420, c_2])).
% 8.61/2.85  tff(c_3582, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_129, c_3562])).
% 8.61/2.85  tff(c_3604, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_3582])).
% 8.61/2.85  tff(c_18, plain, (![A_12, C_27]: (r2_hidden(k4_tarski('#skF_5'(A_12, k2_relat_1(A_12), C_27), C_27), A_12) | ~r2_hidden(C_27, k2_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_95, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_9'(D_40), D_40), '#skF_8') | ~r2_hidden(D_40, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_63, c_44])).
% 8.61/2.85  tff(c_1424, plain, (![A_191, B_192, D_193]: (r2_hidden(k4_tarski('#skF_3'(A_191, B_192), '#skF_2'(A_191, B_192)), A_191) | ~r2_hidden(k4_tarski(D_193, '#skF_4'(A_191, B_192)), A_191) | k2_relat_1(A_191)=B_192)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_1553, plain, (![B_198]: (r2_hidden(k4_tarski('#skF_3'('#skF_8', B_198), '#skF_2'('#skF_8', B_198)), '#skF_8') | k2_relat_1('#skF_8')=B_198 | ~r2_hidden('#skF_4'('#skF_8', B_198), '#skF_7'))), inference(resolution, [status(thm)], [c_95, c_1424])).
% 8.61/2.85  tff(c_5534, plain, (![B_355]: (r2_hidden('#skF_2'('#skF_8', B_355), k2_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_355 | ~r2_hidden('#skF_4'('#skF_8', B_355), '#skF_7'))), inference(resolution, [status(thm)], [c_1553, c_20])).
% 8.61/2.85  tff(c_2013, plain, (![C_223]: (r2_hidden(C_223, '#skF_7') | ~r2_hidden(C_223, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_1971, c_522])).
% 8.61/2.85  tff(c_6981, plain, (![B_405]: (r2_hidden('#skF_2'('#skF_8', B_405), '#skF_7') | k2_relat_1('#skF_8')=B_405 | ~r2_hidden('#skF_4'('#skF_8', B_405), '#skF_7'))), inference(resolution, [status(thm)], [c_5534, c_2013])).
% 8.61/2.85  tff(c_22, plain, (![A_12, B_13, D_26]: (~r2_hidden('#skF_2'(A_12, B_13), B_13) | ~r2_hidden(k4_tarski(D_26, '#skF_4'(A_12, B_13)), A_12) | k2_relat_1(A_12)=B_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_6990, plain, (![D_26]: (~r2_hidden(k4_tarski(D_26, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7'))), inference(resolution, [status(thm)], [c_6981, c_22])).
% 8.61/2.85  tff(c_7008, plain, (![D_26]: (~r2_hidden(k4_tarski(D_26, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3396, c_6990])).
% 8.61/2.85  tff(c_7016, plain, (![D_406]: (~r2_hidden(k4_tarski(D_406, '#skF_4'('#skF_8', '#skF_7')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_148, c_7008])).
% 8.61/2.85  tff(c_7024, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18, c_7016])).
% 8.61/2.85  tff(c_7037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3604, c_7024])).
% 8.61/2.85  tff(c_7038, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 8.61/2.85  tff(c_7039, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_38])).
% 8.61/2.85  tff(c_7078, plain, (![A_428, B_429, C_430]: (k2_relset_1(A_428, B_429, C_430)=k2_relat_1(C_430) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(A_428, B_429))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.61/2.85  tff(c_7085, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_7078])).
% 8.61/2.85  tff(c_7088, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_7039, c_7085])).
% 8.61/2.85  tff(c_7115, plain, (![A_438, C_439]: (r2_hidden(k4_tarski('#skF_5'(A_438, k2_relat_1(A_438), C_439), C_439), A_438) | ~r2_hidden(C_439, k2_relat_1(A_438)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.61/2.85  tff(c_34, plain, (![E_43]: (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski(E_43, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.61/2.85  tff(c_7064, plain, (![E_43]: (~r2_hidden(k4_tarski(E_43, '#skF_10'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7039, c_34])).
% 8.61/2.85  tff(c_7127, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_7115, c_7064])).
% 8.61/2.85  tff(c_7141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7038, c_7088, c_7127])).
% 8.61/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.61/2.85  
% 8.61/2.85  Inference rules
% 8.61/2.85  ----------------------
% 8.61/2.85  #Ref     : 0
% 8.61/2.85  #Sup     : 1709
% 8.61/2.85  #Fact    : 0
% 8.61/2.85  #Define  : 0
% 8.61/2.85  #Split   : 29
% 8.61/2.85  #Chain   : 0
% 8.61/2.85  #Close   : 0
% 8.61/2.85  
% 8.61/2.85  Ordering : KBO
% 8.61/2.85  
% 8.61/2.85  Simplification rules
% 8.61/2.86  ----------------------
% 8.61/2.86  #Subsume      : 414
% 8.61/2.86  #Demod        : 188
% 8.61/2.86  #Tautology    : 161
% 8.61/2.86  #SimpNegUnit  : 13
% 8.61/2.86  #BackRed      : 9
% 8.61/2.86  
% 8.61/2.86  #Partial instantiations: 0
% 8.61/2.86  #Strategies tried      : 1
% 8.61/2.86  
% 8.61/2.86  Timing (in seconds)
% 8.61/2.86  ----------------------
% 8.61/2.86  Preprocessing        : 0.32
% 8.61/2.86  Parsing              : 0.16
% 8.61/2.86  CNF conversion       : 0.03
% 8.61/2.86  Main loop            : 1.78
% 8.61/2.86  Inferencing          : 0.49
% 8.61/2.86  Reduction            : 0.42
% 8.61/2.86  Demodulation         : 0.26
% 8.61/2.86  BG Simplification    : 0.06
% 8.61/2.86  Subsumption          : 0.66
% 8.61/2.86  Abstraction          : 0.08
% 8.61/2.86  MUC search           : 0.00
% 8.61/2.86  Cooper               : 0.00
% 8.61/2.86  Total                : 2.13
% 8.61/2.86  Index Insertion      : 0.00
% 8.61/2.86  Index Deletion       : 0.00
% 8.61/2.86  Index Matching       : 0.00
% 8.61/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
