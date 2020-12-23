%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0841+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:56 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 335 expanded)
%              Number of leaves         :   31 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 ( 990 expanded)
%              Number of equality atoms :   14 (  39 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(F,E),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    ! [C_155,A_156,B_157] :
      ( v1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_68,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_3036,plain,(
    ! [A_690,B_691,D_692] :
      ( r2_hidden(k4_tarski('#skF_4'(A_690,B_691,k9_relat_1(A_690,B_691),D_692),D_692),A_690)
      | ~ r2_hidden(D_692,k9_relat_1(A_690,B_691))
      | ~ v1_relat_1(A_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2354,plain,(
    ! [A_551,B_552,C_553,D_554] :
      ( k7_relset_1(A_551,B_552,C_553,D_554) = k9_relat_1(C_553,D_554)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_551,B_552))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2357,plain,(
    ! [D_554] : k7_relset_1('#skF_7','#skF_5','#skF_8',D_554) = k9_relat_1('#skF_8',D_554) ),
    inference(resolution,[status(thm)],[c_40,c_2354])).

tff(c_2264,plain,(
    ! [A_525,B_526,D_527] :
      ( r2_hidden(k4_tarski('#skF_4'(A_525,B_526,k9_relat_1(A_525,B_526),D_527),D_527),A_525)
      | ~ r2_hidden(D_527,k9_relat_1(A_525,B_526))
      | ~ v1_relat_1(A_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1176,plain,(
    ! [A_353,B_354,C_355,D_356] :
      ( k7_relset_1(A_353,B_354,C_355,D_356) = k9_relat_1(C_355,D_356)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1179,plain,(
    ! [D_356] : k7_relset_1('#skF_7','#skF_5','#skF_8',D_356) = k9_relat_1('#skF_8',D_356) ),
    inference(resolution,[status(thm)],[c_40,c_1176])).

tff(c_331,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k7_relset_1(A_229,B_230,C_231,D_232) = k9_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [D_232] : k7_relset_1('#skF_7','#skF_5','#skF_8',D_232) = k9_relat_1('#skF_8',D_232) ),
    inference(resolution,[status(thm)],[c_40,c_331])).

tff(c_62,plain,
    ( r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_84,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6'))
    | r2_hidden('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    r2_hidden('#skF_10','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,
    ( r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6'))
    | r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_94,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_161,plain,(
    ! [D_194,A_195,B_196,E_197] :
      ( r2_hidden(D_194,k9_relat_1(A_195,B_196))
      | ~ r2_hidden(E_197,B_196)
      | ~ r2_hidden(k4_tarski(E_197,D_194),A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_177,plain,(
    ! [D_198,A_199] :
      ( r2_hidden(D_198,k9_relat_1(A_199,'#skF_6'))
      | ~ r2_hidden(k4_tarski('#skF_10',D_198),A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(resolution,[status(thm)],[c_74,c_161])).

tff(c_184,plain,
    ( r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_177])).

tff(c_192,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_184])).

tff(c_118,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k7_relset_1(A_179,B_180,C_181,D_182) = k9_relat_1(C_181,D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    ! [D_182] : k7_relset_1('#skF_7','#skF_5','#skF_8',D_182) = k9_relat_1('#skF_8',D_182) ),
    inference(resolution,[status(thm)],[c_40,c_118])).

tff(c_48,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_152,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | ~ r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_288,plain,(
    ! [F_215] :
      ( ~ r2_hidden(F_215,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_215,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_215,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_121,c_48])).

tff(c_291,plain,
    ( ~ r2_hidden('#skF_10','#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_288])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_74,c_291])).

tff(c_299,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_336,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_299])).

tff(c_547,plain,(
    ! [A_280,B_281,D_282] :
      ( r2_hidden(k4_tarski('#skF_4'(A_280,B_281,k9_relat_1(A_280,B_281),D_282),D_282),A_280)
      | ~ r2_hidden(D_282,k9_relat_1(A_280,B_281))
      | ~ v1_relat_1(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [C_160,B_161,A_162] :
      ( ~ v1_xboole_0(C_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(C_160))
      | ~ r2_hidden(A_162,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_82,plain,(
    ! [A_162] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_162,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_83,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_90,plain,(
    ! [A_167,C_168,B_169] :
      ( m1_subset_1(A_167,C_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(C_168))
      | ~ r2_hidden(A_167,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_93,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_167,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_90])).

tff(c_32,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_310,plain,(
    ! [A_216,C_217,B_218,D_219] :
      ( r2_hidden(A_216,C_217)
      | ~ r2_hidden(k4_tarski(A_216,B_218),k2_zfmisc_1(C_217,D_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_376,plain,(
    ! [A_240,C_241,D_242,B_243] :
      ( r2_hidden(A_240,C_241)
      | v1_xboole_0(k2_zfmisc_1(C_241,D_242))
      | ~ m1_subset_1(k4_tarski(A_240,B_243),k2_zfmisc_1(C_241,D_242)) ) ),
    inference(resolution,[status(thm)],[c_32,c_310])).

tff(c_383,plain,(
    ! [A_240,B_243] :
      ( r2_hidden(A_240,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_240,B_243),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_93,c_376])).

tff(c_387,plain,(
    ! [A_240,B_243] :
      ( r2_hidden(A_240,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_240,B_243),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_383])).

tff(c_561,plain,(
    ! [B_281,D_282] :
      ( r2_hidden('#skF_4'('#skF_8',B_281,k9_relat_1('#skF_8',B_281),D_282),'#skF_7')
      | ~ r2_hidden(D_282,k9_relat_1('#skF_8',B_281))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_547,c_387])).

tff(c_773,plain,(
    ! [B_298,D_299] :
      ( r2_hidden('#skF_4'('#skF_8',B_298,k9_relat_1('#skF_8',B_298),D_299),'#skF_7')
      | ~ r2_hidden(D_299,k9_relat_1('#skF_8',B_298)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_561])).

tff(c_30,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_780,plain,(
    ! [B_298,D_299] :
      ( m1_subset_1('#skF_4'('#skF_8',B_298,k9_relat_1('#skF_8',B_298),D_299),'#skF_7')
      | ~ r2_hidden(D_299,k9_relat_1('#skF_8',B_298)) ) ),
    inference(resolution,[status(thm)],[c_773,c_30])).

tff(c_6,plain,(
    ! [A_4,B_27,D_42] :
      ( r2_hidden('#skF_4'(A_4,B_27,k9_relat_1(A_4,B_27),D_42),B_27)
      | ~ r2_hidden(D_42,k9_relat_1(A_4,B_27))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_300,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_152,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_393,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_152,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_56])).

tff(c_557,plain,(
    ! [B_281] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_281,k9_relat_1('#skF_8',B_281),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_281,k9_relat_1('#skF_8',B_281),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8',B_281))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_547,c_393])).

tff(c_1111,plain,(
    ! [B_330] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_330,k9_relat_1('#skF_8',B_330),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_330,k9_relat_1('#skF_8',B_330),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8',B_330)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_557])).

tff(c_1115,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k9_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_1111])).

tff(c_1121,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k9_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_336,c_1115])).

tff(c_1127,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_780,c_1121])).

tff(c_1131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_1127])).

tff(c_1132,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1182,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_1132])).

tff(c_1391,plain,(
    ! [A_403,B_404,D_405] :
      ( r2_hidden(k4_tarski('#skF_4'(A_403,B_404,k9_relat_1(A_403,B_404),D_405),D_405),A_403)
      | ~ r2_hidden(D_405,k9_relat_1(A_403,B_404))
      | ~ v1_relat_1(A_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1138,plain,(
    ! [A_331,C_332,B_333] :
      ( m1_subset_1(A_331,C_332)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(C_332))
      | ~ r2_hidden(A_331,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1141,plain,(
    ! [A_331] :
      ( m1_subset_1(A_331,k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_331,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_1138])).

tff(c_1148,plain,(
    ! [A_339,C_340,B_341,D_342] :
      ( r2_hidden(A_339,C_340)
      | ~ r2_hidden(k4_tarski(A_339,B_341),k2_zfmisc_1(C_340,D_342)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1197,plain,(
    ! [A_358,C_359,D_360,B_361] :
      ( r2_hidden(A_358,C_359)
      | v1_xboole_0(k2_zfmisc_1(C_359,D_360))
      | ~ m1_subset_1(k4_tarski(A_358,B_361),k2_zfmisc_1(C_359,D_360)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1148])).

tff(c_1204,plain,(
    ! [A_358,B_361] :
      ( r2_hidden(A_358,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_358,B_361),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1141,c_1197])).

tff(c_1208,plain,(
    ! [A_358,B_361] :
      ( r2_hidden(A_358,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_358,B_361),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1204])).

tff(c_1403,plain,(
    ! [B_404,D_405] :
      ( r2_hidden('#skF_4'('#skF_8',B_404,k9_relat_1('#skF_8',B_404),D_405),'#skF_7')
      | ~ r2_hidden(D_405,k9_relat_1('#skF_8',B_404))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1391,c_1208])).

tff(c_1584,plain,(
    ! [B_419,D_420] :
      ( r2_hidden('#skF_4'('#skF_8',B_419,k9_relat_1('#skF_8',B_419),D_420),'#skF_7')
      | ~ r2_hidden(D_420,k9_relat_1('#skF_8',B_419)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1403])).

tff(c_1591,plain,(
    ! [B_419,D_420] :
      ( m1_subset_1('#skF_4'('#skF_8',B_419,k9_relat_1('#skF_8',B_419),D_420),'#skF_7')
      | ~ r2_hidden(D_420,k9_relat_1('#skF_8',B_419)) ) ),
    inference(resolution,[status(thm)],[c_1584,c_30])).

tff(c_1133,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_152,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1154,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_152,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1133,c_60])).

tff(c_1407,plain,(
    ! [B_404] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_404,k9_relat_1('#skF_8',B_404),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_404,k9_relat_1('#skF_8',B_404),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8',B_404))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1391,c_1154])).

tff(c_2055,plain,(
    ! [B_462] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_462,k9_relat_1('#skF_8',B_462),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_462,k9_relat_1('#skF_8',B_462),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8',B_462)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1407])).

tff(c_2059,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k9_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_2055])).

tff(c_2065,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k9_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1182,c_2059])).

tff(c_2071,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1591,c_2065])).

tff(c_2075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_2071])).

tff(c_2076,plain,(
    ! [A_162] : ~ r2_hidden(A_162,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2290,plain,(
    ! [D_527,B_526] :
      ( ~ r2_hidden(D_527,k9_relat_1('#skF_8',B_526))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2264,c_2076])).

tff(c_2302,plain,(
    ! [D_527,B_526] : ~ r2_hidden(D_527,k9_relat_1('#skF_8',B_526)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2290])).

tff(c_2120,plain,(
    ! [A_484,B_485,C_486,D_487] :
      ( k7_relset_1(A_484,B_485,C_486,D_487) = k9_relat_1(C_486,D_487)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(A_484,B_485))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2123,plain,(
    ! [D_487] : k7_relset_1('#skF_7','#skF_5','#skF_8',D_487) = k9_relat_1('#skF_8',D_487) ),
    inference(resolution,[status(thm)],[c_40,c_2120])).

tff(c_2096,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2076,c_58])).

tff(c_2126,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2096])).

tff(c_2305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2302,c_2126])).

tff(c_2306,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_7','#skF_5','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2359,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_2306])).

tff(c_2478,plain,(
    ! [A_588,B_589,D_590] :
      ( r2_hidden(k4_tarski('#skF_4'(A_588,B_589,k9_relat_1(A_588,B_589),D_590),D_590),A_588)
      | ~ r2_hidden(D_590,k9_relat_1(A_588,B_589))
      | ~ v1_relat_1(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2319,plain,(
    ! [C_528,B_529,A_530] :
      ( ~ v1_xboole_0(C_528)
      | ~ m1_subset_1(B_529,k1_zfmisc_1(C_528))
      | ~ r2_hidden(A_530,B_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2322,plain,(
    ! [A_530] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_530,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_2319])).

tff(c_2323,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2322])).

tff(c_2334,plain,(
    ! [A_539,C_540,B_541] :
      ( m1_subset_1(A_539,C_540)
      | ~ m1_subset_1(B_541,k1_zfmisc_1(C_540))
      | ~ r2_hidden(A_539,B_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2337,plain,(
    ! [A_539] :
      ( m1_subset_1(A_539,k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(A_539,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_2334])).

tff(c_2329,plain,(
    ! [A_535,C_536,B_537,D_538] :
      ( r2_hidden(A_535,C_536)
      | ~ r2_hidden(k4_tarski(A_535,B_537),k2_zfmisc_1(C_536,D_538)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2411,plain,(
    ! [A_568,C_569,D_570,B_571] :
      ( r2_hidden(A_568,C_569)
      | v1_xboole_0(k2_zfmisc_1(C_569,D_570))
      | ~ m1_subset_1(k4_tarski(A_568,B_571),k2_zfmisc_1(C_569,D_570)) ) ),
    inference(resolution,[status(thm)],[c_32,c_2329])).

tff(c_2418,plain,(
    ! [A_568,B_571] :
      ( r2_hidden(A_568,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_568,B_571),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2337,c_2411])).

tff(c_2422,plain,(
    ! [A_568,B_571] :
      ( r2_hidden(A_568,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_568,B_571),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_2418])).

tff(c_2484,plain,(
    ! [B_589,D_590] :
      ( r2_hidden('#skF_4'('#skF_8',B_589,k9_relat_1('#skF_8',B_589),D_590),'#skF_7')
      | ~ r2_hidden(D_590,k9_relat_1('#skF_8',B_589))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2478,c_2422])).

tff(c_2624,plain,(
    ! [B_602,D_603] :
      ( r2_hidden('#skF_4'('#skF_8',B_602,k9_relat_1('#skF_8',B_602),D_603),'#skF_7')
      | ~ r2_hidden(D_603,k9_relat_1('#skF_8',B_602)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2484])).

tff(c_2632,plain,(
    ! [B_604,D_605] :
      ( m1_subset_1('#skF_4'('#skF_8',B_604,k9_relat_1('#skF_8',B_604),D_605),'#skF_7')
      | ~ r2_hidden(D_605,k9_relat_1('#skF_8',B_604)) ) ),
    inference(resolution,[status(thm)],[c_2624,c_30])).

tff(c_2307,plain,(
    ~ r2_hidden('#skF_10','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_152,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | r2_hidden('#skF_10','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2375,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski(F_152,'#skF_9'),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2307,c_52])).

tff(c_2494,plain,(
    ! [B_589] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_589,k9_relat_1('#skF_8',B_589),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_589,k9_relat_1('#skF_8',B_589),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8',B_589))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2478,c_2375])).

tff(c_2573,plain,(
    ! [B_595] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_595,k9_relat_1('#skF_8',B_595),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_595,k9_relat_1('#skF_8',B_595),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8',B_595)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2494])).

tff(c_2577,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k9_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_2573])).

tff(c_2583,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k9_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2359,c_2577])).

tff(c_2635,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2632,c_2583])).

tff(c_2639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2359,c_2635])).

tff(c_2640,plain,(
    ! [A_530] : ~ r2_hidden(A_530,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2322])).

tff(c_3060,plain,(
    ! [D_692,B_691] :
      ( ~ r2_hidden(D_692,k9_relat_1('#skF_8',B_691))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3036,c_2640])).

tff(c_3082,plain,(
    ! [D_692,B_691] : ~ r2_hidden(D_692,k9_relat_1('#skF_8',B_691)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3060])).

tff(c_2680,plain,(
    ! [A_627,B_628,C_629,D_630] :
      ( k7_relset_1(A_627,B_628,C_629,D_630) = k9_relat_1(C_629,D_630)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(A_627,B_628))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2683,plain,(
    ! [D_630] : k7_relset_1('#skF_7','#skF_5','#skF_8',D_630) = k9_relat_1('#skF_8',D_630) ),
    inference(resolution,[status(thm)],[c_40,c_2680])).

tff(c_2685,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2683,c_2306])).

tff(c_3089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3082,c_2685])).

%------------------------------------------------------------------------------
