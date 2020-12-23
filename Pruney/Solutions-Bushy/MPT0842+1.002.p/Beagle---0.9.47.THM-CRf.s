%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0842+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:57 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.50s
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
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k8_relset_1(A,C,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(E,F),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_7'))) ),
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
    ! [D_690,A_691,B_692] :
      ( r2_hidden(k4_tarski(D_690,'#skF_4'(A_691,B_692,k10_relat_1(A_691,B_692),D_690)),A_691)
      | ~ r2_hidden(D_690,k10_relat_1(A_691,B_692))
      | ~ v1_relat_1(A_691) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2354,plain,(
    ! [A_551,B_552,C_553,D_554] :
      ( k8_relset_1(A_551,B_552,C_553,D_554) = k10_relat_1(C_553,D_554)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_551,B_552))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2357,plain,(
    ! [D_554] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_554) = k10_relat_1('#skF_8',D_554) ),
    inference(resolution,[status(thm)],[c_40,c_2354])).

tff(c_2264,plain,(
    ! [D_525,A_526,B_527] :
      ( r2_hidden(k4_tarski(D_525,'#skF_4'(A_526,B_527,k10_relat_1(A_526,B_527),D_525)),A_526)
      | ~ r2_hidden(D_525,k10_relat_1(A_526,B_527))
      | ~ v1_relat_1(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1176,plain,(
    ! [A_353,B_354,C_355,D_356] :
      ( k8_relset_1(A_353,B_354,C_355,D_356) = k10_relat_1(C_355,D_356)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1179,plain,(
    ! [D_356] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_356) = k10_relat_1('#skF_8',D_356) ),
    inference(resolution,[status(thm)],[c_40,c_1176])).

tff(c_331,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k8_relset_1(A_229,B_230,C_231,D_232) = k10_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [D_232] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_232) = k10_relat_1('#skF_8',D_232) ),
    inference(resolution,[status(thm)],[c_40,c_331])).

tff(c_62,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_84,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | r2_hidden('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    r2_hidden('#skF_10','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_94,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_161,plain,(
    ! [D_194,A_195,B_196,E_197] :
      ( r2_hidden(D_194,k10_relat_1(A_195,B_196))
      | ~ r2_hidden(E_197,B_196)
      | ~ r2_hidden(k4_tarski(D_194,E_197),A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_177,plain,(
    ! [D_198,A_199] :
      ( r2_hidden(D_198,k10_relat_1(A_199,'#skF_6'))
      | ~ r2_hidden(k4_tarski(D_198,'#skF_10'),A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(resolution,[status(thm)],[c_74,c_161])).

tff(c_184,plain,
    ( r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_94,c_177])).

tff(c_192,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_184])).

tff(c_118,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k8_relset_1(A_179,B_180,C_181,D_182) = k10_relat_1(C_181,D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    ! [D_182] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_182) = k10_relat_1('#skF_8',D_182) ),
    inference(resolution,[status(thm)],[c_40,c_118])).

tff(c_48,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_152),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | ~ r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_288,plain,(
    ! [F_215] :
      ( ~ r2_hidden(F_215,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_215),'#skF_8')
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
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_336,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_299])).

tff(c_547,plain,(
    ! [D_280,A_281,B_282] :
      ( r2_hidden(k4_tarski(D_280,'#skF_4'(A_281,B_282,k10_relat_1(A_281,B_282),D_280)),A_281)
      | ~ r2_hidden(D_280,k10_relat_1(A_281,B_282))
      | ~ v1_relat_1(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [C_160,B_161,A_162] :
      ( ~ v1_xboole_0(C_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(C_160))
      | ~ r2_hidden(A_162,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_82,plain,(
    ! [A_162] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(A_162,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_79])).

tff(c_83,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_90,plain,(
    ! [A_167,C_168,B_169] :
      ( m1_subset_1(A_167,C_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(C_168))
      | ~ r2_hidden(A_167,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_93,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(A_167,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_90])).

tff(c_32,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [B_163,D_164,A_165,C_166] :
      ( r2_hidden(B_163,D_164)
      | ~ r2_hidden(k4_tarski(A_165,B_163),k2_zfmisc_1(C_166,D_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_401,plain,(
    ! [B_247,D_248,C_249,A_250] :
      ( r2_hidden(B_247,D_248)
      | v1_xboole_0(k2_zfmisc_1(C_249,D_248))
      | ~ m1_subset_1(k4_tarski(A_250,B_247),k2_zfmisc_1(C_249,D_248)) ) ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_408,plain,(
    ! [B_247,A_250] :
      ( r2_hidden(B_247,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(k4_tarski(A_250,B_247),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_93,c_401])).

tff(c_412,plain,(
    ! [B_247,A_250] :
      ( r2_hidden(B_247,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_250,B_247),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_408])).

tff(c_553,plain,(
    ! [B_282,D_280] :
      ( r2_hidden('#skF_4'('#skF_8',B_282,k10_relat_1('#skF_8',B_282),D_280),'#skF_7')
      | ~ r2_hidden(D_280,k10_relat_1('#skF_8',B_282))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_547,c_412])).

tff(c_773,plain,(
    ! [B_298,D_299] :
      ( r2_hidden('#skF_4'('#skF_8',B_298,k10_relat_1('#skF_8',B_298),D_299),'#skF_7')
      | ~ r2_hidden(D_299,k10_relat_1('#skF_8',B_298)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_553])).

tff(c_30,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_780,plain,(
    ! [B_298,D_299] :
      ( m1_subset_1('#skF_4'('#skF_8',B_298,k10_relat_1('#skF_8',B_298),D_299),'#skF_7')
      | ~ r2_hidden(D_299,k10_relat_1('#skF_8',B_298)) ) ),
    inference(resolution,[status(thm)],[c_773,c_30])).

tff(c_6,plain,(
    ! [A_4,B_27,D_42] :
      ( r2_hidden('#skF_4'(A_4,B_27,k10_relat_1(A_4,B_27),D_42),B_27)
      | ~ r2_hidden(D_42,k10_relat_1(A_4,B_27))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_300,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_152),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_393,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_152),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_56])).

tff(c_557,plain,(
    ! [B_282] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_282,k10_relat_1('#skF_8',B_282),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_282,k10_relat_1('#skF_8',B_282),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_282))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_547,c_393])).

tff(c_1111,plain,(
    ! [B_330] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_330,k10_relat_1('#skF_8',B_330),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_330,k10_relat_1('#skF_8',B_330),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_330)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_557])).

tff(c_1115,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_1111])).

tff(c_1121,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_336,c_1115])).

tff(c_1127,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_780,c_1121])).

tff(c_1131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_1127])).

tff(c_1132,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1182,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_1132])).

tff(c_1391,plain,(
    ! [D_403,A_404,B_405] :
      ( r2_hidden(k4_tarski(D_403,'#skF_4'(A_404,B_405,k10_relat_1(A_404,B_405),D_403)),A_404)
      | ~ r2_hidden(D_403,k10_relat_1(A_404,B_405))
      | ~ v1_relat_1(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1138,plain,(
    ! [A_331,C_332,B_333] :
      ( m1_subset_1(A_331,C_332)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(C_332))
      | ~ r2_hidden(A_331,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1141,plain,(
    ! [A_331] :
      ( m1_subset_1(A_331,k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(A_331,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_1138])).

tff(c_1142,plain,(
    ! [B_334,D_335,A_336,C_337] :
      ( r2_hidden(B_334,D_335)
      | ~ r2_hidden(k4_tarski(A_336,B_334),k2_zfmisc_1(C_337,D_335)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1215,plain,(
    ! [B_364,D_365,C_366,A_367] :
      ( r2_hidden(B_364,D_365)
      | v1_xboole_0(k2_zfmisc_1(C_366,D_365))
      | ~ m1_subset_1(k4_tarski(A_367,B_364),k2_zfmisc_1(C_366,D_365)) ) ),
    inference(resolution,[status(thm)],[c_32,c_1142])).

tff(c_1222,plain,(
    ! [B_364,A_367] :
      ( r2_hidden(B_364,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(k4_tarski(A_367,B_364),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1141,c_1215])).

tff(c_1226,plain,(
    ! [B_364,A_367] :
      ( r2_hidden(B_364,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_367,B_364),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1222])).

tff(c_1397,plain,(
    ! [B_405,D_403] :
      ( r2_hidden('#skF_4'('#skF_8',B_405,k10_relat_1('#skF_8',B_405),D_403),'#skF_7')
      | ~ r2_hidden(D_403,k10_relat_1('#skF_8',B_405))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1391,c_1226])).

tff(c_1584,plain,(
    ! [B_419,D_420] :
      ( r2_hidden('#skF_4'('#skF_8',B_419,k10_relat_1('#skF_8',B_419),D_420),'#skF_7')
      | ~ r2_hidden(D_420,k10_relat_1('#skF_8',B_419)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1397])).

tff(c_1591,plain,(
    ! [B_419,D_420] :
      ( m1_subset_1('#skF_4'('#skF_8',B_419,k10_relat_1('#skF_8',B_419),D_420),'#skF_7')
      | ~ r2_hidden(D_420,k10_relat_1('#skF_8',B_419)) ) ),
    inference(resolution,[status(thm)],[c_1584,c_30])).

tff(c_1133,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_152),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1154,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_152),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1133,c_60])).

tff(c_1407,plain,(
    ! [B_405] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_405,k10_relat_1('#skF_8',B_405),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_405,k10_relat_1('#skF_8',B_405),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_405))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1391,c_1154])).

tff(c_2055,plain,(
    ! [B_462] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_462,k10_relat_1('#skF_8',B_462),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_462,k10_relat_1('#skF_8',B_462),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_462)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1407])).

tff(c_2059,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_2055])).

tff(c_2065,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1182,c_2059])).

tff(c_2071,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1591,c_2065])).

tff(c_2075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_2071])).

tff(c_2076,plain,(
    ! [A_162] : ~ r2_hidden(A_162,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2290,plain,(
    ! [D_525,B_527] :
      ( ~ r2_hidden(D_525,k10_relat_1('#skF_8',B_527))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2264,c_2076])).

tff(c_2302,plain,(
    ! [D_525,B_527] : ~ r2_hidden(D_525,k10_relat_1('#skF_8',B_527)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2290])).

tff(c_2120,plain,(
    ! [A_484,B_485,C_486,D_487] :
      ( k8_relset_1(A_484,B_485,C_486,D_487) = k10_relat_1(C_486,D_487)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(A_484,B_485))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2123,plain,(
    ! [D_487] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_487) = k10_relat_1('#skF_8',D_487) ),
    inference(resolution,[status(thm)],[c_40,c_2120])).

tff(c_2096,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2076,c_58])).

tff(c_2126,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2123,c_2096])).

tff(c_2305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2302,c_2126])).

tff(c_2306,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2359,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_2306])).

tff(c_2478,plain,(
    ! [D_588,A_589,B_590] :
      ( r2_hidden(k4_tarski(D_588,'#skF_4'(A_589,B_590,k10_relat_1(A_589,B_590),D_588)),A_589)
      | ~ r2_hidden(D_588,k10_relat_1(A_589,B_590))
      | ~ v1_relat_1(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2319,plain,(
    ! [C_528,B_529,A_530] :
      ( ~ v1_xboole_0(C_528)
      | ~ m1_subset_1(B_529,k1_zfmisc_1(C_528))
      | ~ r2_hidden(A_530,B_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2322,plain,(
    ! [A_530] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(A_530,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_2319])).

tff(c_2323,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2322])).

tff(c_2334,plain,(
    ! [A_539,C_540,B_541] :
      ( m1_subset_1(A_539,C_540)
      | ~ m1_subset_1(B_541,k1_zfmisc_1(C_540))
      | ~ r2_hidden(A_539,B_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2337,plain,(
    ! [A_539] :
      ( m1_subset_1(A_539,k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(A_539,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_2334])).

tff(c_2324,plain,(
    ! [B_531,D_532,A_533,C_534] :
      ( r2_hidden(B_531,D_532)
      | ~ r2_hidden(k4_tarski(A_533,B_531),k2_zfmisc_1(C_534,D_532)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2383,plain,(
    ! [B_558,D_559,C_560,A_561] :
      ( r2_hidden(B_558,D_559)
      | v1_xboole_0(k2_zfmisc_1(C_560,D_559))
      | ~ m1_subset_1(k4_tarski(A_561,B_558),k2_zfmisc_1(C_560,D_559)) ) ),
    inference(resolution,[status(thm)],[c_32,c_2324])).

tff(c_2390,plain,(
    ! [B_558,A_561] :
      ( r2_hidden(B_558,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_7'))
      | ~ r2_hidden(k4_tarski(A_561,B_558),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2337,c_2383])).

tff(c_2394,plain,(
    ! [B_558,A_561] :
      ( r2_hidden(B_558,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_561,B_558),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_2390])).

tff(c_2490,plain,(
    ! [B_590,D_588] :
      ( r2_hidden('#skF_4'('#skF_8',B_590,k10_relat_1('#skF_8',B_590),D_588),'#skF_7')
      | ~ r2_hidden(D_588,k10_relat_1('#skF_8',B_590))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2478,c_2394])).

tff(c_2624,plain,(
    ! [B_602,D_603] :
      ( r2_hidden('#skF_4'('#skF_8',B_602,k10_relat_1('#skF_8',B_602),D_603),'#skF_7')
      | ~ r2_hidden(D_603,k10_relat_1('#skF_8',B_602)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2490])).

tff(c_2632,plain,(
    ! [B_604,D_605] :
      ( m1_subset_1('#skF_4'('#skF_8',B_604,k10_relat_1('#skF_8',B_604),D_605),'#skF_7')
      | ~ r2_hidden(D_605,k10_relat_1('#skF_8',B_604)) ) ),
    inference(resolution,[status(thm)],[c_2624,c_30])).

tff(c_2307,plain,(
    ~ r2_hidden('#skF_10','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_152),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7')
      | r2_hidden('#skF_10','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2375,plain,(
    ! [F_152] :
      ( ~ r2_hidden(F_152,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_152),'#skF_8')
      | ~ m1_subset_1(F_152,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2307,c_52])).

tff(c_2494,plain,(
    ! [B_590] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_590,k10_relat_1('#skF_8',B_590),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_590,k10_relat_1('#skF_8',B_590),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_590))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2478,c_2375])).

tff(c_2573,plain,(
    ! [B_595] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_595,k10_relat_1('#skF_8',B_595),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_595,k10_relat_1('#skF_8',B_595),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_595)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2494])).

tff(c_2577,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_2573])).

tff(c_2583,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2359,c_2577])).

tff(c_2635,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2632,c_2583])).

tff(c_2639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2359,c_2635])).

tff(c_2640,plain,(
    ! [A_530] : ~ r2_hidden(A_530,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2322])).

tff(c_3060,plain,(
    ! [D_690,B_692] :
      ( ~ r2_hidden(D_690,k10_relat_1('#skF_8',B_692))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3036,c_2640])).

tff(c_3082,plain,(
    ! [D_690,B_692] : ~ r2_hidden(D_690,k10_relat_1('#skF_8',B_692)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3060])).

tff(c_2680,plain,(
    ! [A_627,B_628,C_629,D_630] :
      ( k8_relset_1(A_627,B_628,C_629,D_630) = k10_relat_1(C_629,D_630)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(A_627,B_628))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2683,plain,(
    ! [D_630] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_630) = k10_relat_1('#skF_8',D_630) ),
    inference(resolution,[status(thm)],[c_40,c_2680])).

tff(c_2685,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2683,c_2306])).

tff(c_3089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3082,c_2685])).

%------------------------------------------------------------------------------
