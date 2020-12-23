%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:35 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 253 expanded)
%              Number of leaves         :   34 ( 100 expanded)
%              Depth                    :    9
%              Number of atoms          :  215 ( 745 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    ! [C_159,B_160,A_161] :
      ( v5_relat_1(C_159,B_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_66,plain,(
    ! [C_156,A_157,B_158] :
      ( v1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_793,plain,(
    ! [A_327,B_328,C_329,D_330] :
      ( k8_relset_1(A_327,B_328,C_329,D_330) = k10_relat_1(C_329,D_330)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_796,plain,(
    ! [D_330] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_330) = k10_relat_1('#skF_9',D_330) ),
    inference(resolution,[status(thm)],[c_42,c_793])).

tff(c_500,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k8_relset_1(A_264,B_265,C_266,D_267) = k10_relat_1(C_266,D_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_503,plain,(
    ! [D_267] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_267) = k10_relat_1('#skF_9',D_267) ),
    inference(resolution,[status(thm)],[c_42,c_500])).

tff(c_250,plain,(
    ! [A_213,B_214,C_215,D_216] :
      ( k8_relset_1(A_213,B_214,C_215,D_216) = k10_relat_1(C_215,D_216)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_253,plain,(
    ! [D_216] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_216) = k10_relat_1('#skF_9',D_216) ),
    inference(resolution,[status(thm)],[c_42,c_250])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_86,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_56,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_76,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_87,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_132,plain,(
    ! [D_185,A_186,B_187,E_188] :
      ( r2_hidden(D_185,k10_relat_1(A_186,B_187))
      | ~ r2_hidden(E_188,B_187)
      | ~ r2_hidden(k4_tarski(D_185,E_188),A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_145,plain,(
    ! [D_189,A_190] :
      ( r2_hidden(D_189,k10_relat_1(A_190,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_189,'#skF_11'),A_190)
      | ~ v1_relat_1(A_190) ) ),
    inference(resolution,[status(thm)],[c_76,c_132])).

tff(c_148,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_87,c_145])).

tff(c_151,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_148])).

tff(c_117,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k8_relset_1(A_177,B_178,C_179,D_180) = k10_relat_1(C_179,D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_120,plain,(
    ! [D_180] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_180) = k10_relat_1('#skF_9',D_180) ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_50,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_205,plain,(
    ! [F_200] :
      ( ~ r2_hidden(F_200,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_200),'#skF_9')
      | ~ m1_subset_1(F_200,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_120,c_50])).

tff(c_212,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_87,c_205])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_76,c_212])).

tff(c_220,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_256,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_220])).

tff(c_236,plain,(
    ! [A_207,B_208,C_209] :
      ( r2_hidden('#skF_5'(A_207,B_208,C_209),k2_relat_1(C_209))
      | ~ r2_hidden(A_207,k10_relat_1(C_209,B_208))
      | ~ v1_relat_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [C_54,A_51,B_52] :
      ( r2_hidden(C_54,A_51)
      | ~ r2_hidden(C_54,k2_relat_1(B_52))
      | ~ v5_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_369,plain,(
    ! [A_241,B_242,C_243,A_244] :
      ( r2_hidden('#skF_5'(A_241,B_242,C_243),A_244)
      | ~ v5_relat_1(C_243,A_244)
      | ~ r2_hidden(A_241,k10_relat_1(C_243,B_242))
      | ~ v1_relat_1(C_243) ) ),
    inference(resolution,[status(thm)],[c_236,c_30])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_407,plain,(
    ! [A_248,B_249,C_250,A_251] :
      ( m1_subset_1('#skF_5'(A_248,B_249,C_250),A_251)
      | ~ v5_relat_1(C_250,A_251)
      | ~ r2_hidden(A_248,k10_relat_1(C_250,B_249))
      | ~ v1_relat_1(C_250) ) ),
    inference(resolution,[status(thm)],[c_369,c_2])).

tff(c_420,plain,(
    ! [A_251] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_251)
      | ~ v5_relat_1('#skF_9',A_251)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_256,c_407])).

tff(c_430,plain,(
    ! [A_251] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_251)
      | ~ v5_relat_1('#skF_9',A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_420])).

tff(c_24,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_5'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(A_45,k10_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden(k4_tarski(A_45,'#skF_5'(A_45,B_46,C_47)),C_47)
      | ~ r2_hidden(A_45,k10_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_221,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_324,plain,(
    ! [F_232] :
      ( ~ r2_hidden(F_232,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_232),'#skF_9')
      | ~ m1_subset_1(F_232,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_58])).

tff(c_328,plain,(
    ! [B_46] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_46,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_46,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_46))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_26,c_324])).

tff(c_453,plain,(
    ! [B_253] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_253,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_253,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_253)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_328])).

tff(c_461,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_453])).

tff(c_467,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_256,c_461])).

tff(c_470,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_430,c_467])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_470])).

tff(c_475,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_505,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_475])).

tff(c_525,plain,(
    ! [A_269,B_270,C_271] :
      ( r2_hidden('#skF_5'(A_269,B_270,C_271),k2_relat_1(C_271))
      | ~ r2_hidden(A_269,k10_relat_1(C_271,B_270))
      | ~ v1_relat_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_630,plain,(
    ! [A_297,B_298,C_299,A_300] :
      ( r2_hidden('#skF_5'(A_297,B_298,C_299),A_300)
      | ~ v5_relat_1(C_299,A_300)
      | ~ r2_hidden(A_297,k10_relat_1(C_299,B_298))
      | ~ v1_relat_1(C_299) ) ),
    inference(resolution,[status(thm)],[c_525,c_30])).

tff(c_666,plain,(
    ! [A_304,B_305,C_306,A_307] :
      ( m1_subset_1('#skF_5'(A_304,B_305,C_306),A_307)
      | ~ v5_relat_1(C_306,A_307)
      | ~ r2_hidden(A_304,k10_relat_1(C_306,B_305))
      | ~ v1_relat_1(C_306) ) ),
    inference(resolution,[status(thm)],[c_630,c_2])).

tff(c_679,plain,(
    ! [A_307] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_307)
      | ~ v5_relat_1('#skF_9',A_307)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_505,c_666])).

tff(c_689,plain,(
    ! [A_307] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_307)
      | ~ v5_relat_1('#skF_9',A_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_679])).

tff(c_534,plain,(
    ! [A_275,B_276,C_277] :
      ( r2_hidden(k4_tarski(A_275,'#skF_5'(A_275,B_276,C_277)),C_277)
      | ~ r2_hidden(A_275,k10_relat_1(C_277,B_276))
      | ~ v1_relat_1(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_476,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_497,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_62])).

tff(c_538,plain,(
    ! [B_276] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_276,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_276,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_276))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_534,c_497])).

tff(c_742,plain,(
    ! [B_314] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_314,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_314,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_314)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_538])).

tff(c_750,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_742])).

tff(c_756,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_505,c_750])).

tff(c_759,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_689,c_756])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_759])).

tff(c_764,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_798,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_764])).

tff(c_818,plain,(
    ! [A_332,B_333,C_334] :
      ( r2_hidden('#skF_5'(A_332,B_333,C_334),k2_relat_1(C_334))
      | ~ r2_hidden(A_332,k10_relat_1(C_334,B_333))
      | ~ v1_relat_1(C_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_910,plain,(
    ! [A_356,B_357,C_358,A_359] :
      ( r2_hidden('#skF_5'(A_356,B_357,C_358),A_359)
      | ~ v5_relat_1(C_358,A_359)
      | ~ r2_hidden(A_356,k10_relat_1(C_358,B_357))
      | ~ v1_relat_1(C_358) ) ),
    inference(resolution,[status(thm)],[c_818,c_30])).

tff(c_946,plain,(
    ! [A_363,B_364,C_365,A_366] :
      ( m1_subset_1('#skF_5'(A_363,B_364,C_365),A_366)
      | ~ v5_relat_1(C_365,A_366)
      | ~ r2_hidden(A_363,k10_relat_1(C_365,B_364))
      | ~ v1_relat_1(C_365) ) ),
    inference(resolution,[status(thm)],[c_910,c_2])).

tff(c_959,plain,(
    ! [A_366] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_366)
      | ~ v5_relat_1('#skF_9',A_366)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_798,c_946])).

tff(c_969,plain,(
    ! [A_366] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_366)
      | ~ v5_relat_1('#skF_9',A_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_959])).

tff(c_829,plain,(
    ! [A_339,B_340,C_341] :
      ( r2_hidden(k4_tarski(A_339,'#skF_5'(A_339,B_340,C_341)),C_341)
      | ~ r2_hidden(A_339,k10_relat_1(C_341,B_340))
      | ~ v1_relat_1(C_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_765,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_826,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_153),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_54])).

tff(c_833,plain,(
    ! [B_340] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_340,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_340,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_340))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_829,c_826])).

tff(c_1001,plain,(
    ! [B_373] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_373,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_373,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_373)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_833])).

tff(c_1009,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_1001])).

tff(c_1015,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_798,c_1009])).

tff(c_1018,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_969,c_1015])).

tff(c_1022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.52  
% 2.96/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.52  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.96/1.52  
% 2.96/1.52  %Foreground sorts:
% 2.96/1.52  
% 2.96/1.52  
% 2.96/1.52  %Background operators:
% 2.96/1.52  
% 2.96/1.52  
% 2.96/1.52  %Foreground operators:
% 2.96/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.96/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.52  tff('#skF_11', type, '#skF_11': $i).
% 2.96/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.96/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.96/1.52  tff('#skF_7', type, '#skF_7': $i).
% 2.96/1.52  tff('#skF_10', type, '#skF_10': $i).
% 2.96/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.96/1.52  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.96/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.96/1.52  tff('#skF_9', type, '#skF_9': $i).
% 2.96/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.96/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.96/1.52  tff('#skF_8', type, '#skF_8': $i).
% 2.96/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.96/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.96/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.96/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.52  
% 3.30/1.54  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 3.30/1.54  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.30/1.54  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.30/1.54  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.30/1.54  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 3.30/1.54  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.30/1.54  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 3.30/1.54  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.30/1.54  tff(c_42, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_71, plain, (![C_159, B_160, A_161]: (v5_relat_1(C_159, B_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.30/1.54  tff(c_75, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_42, c_71])).
% 3.30/1.54  tff(c_66, plain, (![C_156, A_157, B_158]: (v1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.30/1.54  tff(c_70, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_66])).
% 3.30/1.54  tff(c_793, plain, (![A_327, B_328, C_329, D_330]: (k8_relset_1(A_327, B_328, C_329, D_330)=k10_relat_1(C_329, D_330) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.54  tff(c_796, plain, (![D_330]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_330)=k10_relat_1('#skF_9', D_330))), inference(resolution, [status(thm)], [c_42, c_793])).
% 3.30/1.54  tff(c_500, plain, (![A_264, B_265, C_266, D_267]: (k8_relset_1(A_264, B_265, C_266, D_267)=k10_relat_1(C_266, D_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.54  tff(c_503, plain, (![D_267]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_267)=k10_relat_1('#skF_9', D_267))), inference(resolution, [status(thm)], [c_42, c_500])).
% 3.30/1.54  tff(c_250, plain, (![A_213, B_214, C_215, D_216]: (k8_relset_1(A_213, B_214, C_215, D_216)=k10_relat_1(C_215, D_216) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.54  tff(c_253, plain, (![D_216]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_216)=k10_relat_1('#skF_9', D_216))), inference(resolution, [status(thm)], [c_42, c_250])).
% 3.30/1.54  tff(c_64, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_86, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_64])).
% 3.30/1.54  tff(c_56, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_76, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_56])).
% 3.30/1.54  tff(c_60, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_87, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_60])).
% 3.30/1.54  tff(c_132, plain, (![D_185, A_186, B_187, E_188]: (r2_hidden(D_185, k10_relat_1(A_186, B_187)) | ~r2_hidden(E_188, B_187) | ~r2_hidden(k4_tarski(D_185, E_188), A_186) | ~v1_relat_1(A_186))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.30/1.54  tff(c_145, plain, (![D_189, A_190]: (r2_hidden(D_189, k10_relat_1(A_190, '#skF_7')) | ~r2_hidden(k4_tarski(D_189, '#skF_11'), A_190) | ~v1_relat_1(A_190))), inference(resolution, [status(thm)], [c_76, c_132])).
% 3.30/1.54  tff(c_148, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_87, c_145])).
% 3.30/1.54  tff(c_151, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_148])).
% 3.30/1.54  tff(c_117, plain, (![A_177, B_178, C_179, D_180]: (k8_relset_1(A_177, B_178, C_179, D_180)=k10_relat_1(C_179, D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.54  tff(c_120, plain, (![D_180]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_180)=k10_relat_1('#skF_9', D_180))), inference(resolution, [status(thm)], [c_42, c_117])).
% 3.30/1.54  tff(c_50, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_153), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_205, plain, (![F_200]: (~r2_hidden(F_200, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_200), '#skF_9') | ~m1_subset_1(F_200, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_120, c_50])).
% 3.30/1.54  tff(c_212, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_87, c_205])).
% 3.30/1.54  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_76, c_212])).
% 3.30/1.54  tff(c_220, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 3.30/1.54  tff(c_256, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_220])).
% 3.30/1.54  tff(c_236, plain, (![A_207, B_208, C_209]: (r2_hidden('#skF_5'(A_207, B_208, C_209), k2_relat_1(C_209)) | ~r2_hidden(A_207, k10_relat_1(C_209, B_208)) | ~v1_relat_1(C_209))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_30, plain, (![C_54, A_51, B_52]: (r2_hidden(C_54, A_51) | ~r2_hidden(C_54, k2_relat_1(B_52)) | ~v5_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.30/1.54  tff(c_369, plain, (![A_241, B_242, C_243, A_244]: (r2_hidden('#skF_5'(A_241, B_242, C_243), A_244) | ~v5_relat_1(C_243, A_244) | ~r2_hidden(A_241, k10_relat_1(C_243, B_242)) | ~v1_relat_1(C_243))), inference(resolution, [status(thm)], [c_236, c_30])).
% 3.30/1.54  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.30/1.54  tff(c_407, plain, (![A_248, B_249, C_250, A_251]: (m1_subset_1('#skF_5'(A_248, B_249, C_250), A_251) | ~v5_relat_1(C_250, A_251) | ~r2_hidden(A_248, k10_relat_1(C_250, B_249)) | ~v1_relat_1(C_250))), inference(resolution, [status(thm)], [c_369, c_2])).
% 3.30/1.54  tff(c_420, plain, (![A_251]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_251) | ~v5_relat_1('#skF_9', A_251) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_256, c_407])).
% 3.30/1.54  tff(c_430, plain, (![A_251]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_251) | ~v5_relat_1('#skF_9', A_251))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_420])).
% 3.30/1.54  tff(c_24, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_5'(A_45, B_46, C_47), B_46) | ~r2_hidden(A_45, k10_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_26, plain, (![A_45, B_46, C_47]: (r2_hidden(k4_tarski(A_45, '#skF_5'(A_45, B_46, C_47)), C_47) | ~r2_hidden(A_45, k10_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_221, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_60])).
% 3.30/1.54  tff(c_58, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_153), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_324, plain, (![F_232]: (~r2_hidden(F_232, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_232), '#skF_9') | ~m1_subset_1(F_232, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_221, c_58])).
% 3.30/1.54  tff(c_328, plain, (![B_46]: (~r2_hidden('#skF_5'('#skF_10', B_46, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_46, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_46)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_26, c_324])).
% 3.30/1.54  tff(c_453, plain, (![B_253]: (~r2_hidden('#skF_5'('#skF_10', B_253, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_253, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_253)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_328])).
% 3.30/1.54  tff(c_461, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_453])).
% 3.30/1.54  tff(c_467, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_256, c_461])).
% 3.30/1.54  tff(c_470, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_430, c_467])).
% 3.30/1.54  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_470])).
% 3.30/1.54  tff(c_475, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 3.30/1.54  tff(c_505, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_475])).
% 3.30/1.54  tff(c_525, plain, (![A_269, B_270, C_271]: (r2_hidden('#skF_5'(A_269, B_270, C_271), k2_relat_1(C_271)) | ~r2_hidden(A_269, k10_relat_1(C_271, B_270)) | ~v1_relat_1(C_271))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_630, plain, (![A_297, B_298, C_299, A_300]: (r2_hidden('#skF_5'(A_297, B_298, C_299), A_300) | ~v5_relat_1(C_299, A_300) | ~r2_hidden(A_297, k10_relat_1(C_299, B_298)) | ~v1_relat_1(C_299))), inference(resolution, [status(thm)], [c_525, c_30])).
% 3.30/1.54  tff(c_666, plain, (![A_304, B_305, C_306, A_307]: (m1_subset_1('#skF_5'(A_304, B_305, C_306), A_307) | ~v5_relat_1(C_306, A_307) | ~r2_hidden(A_304, k10_relat_1(C_306, B_305)) | ~v1_relat_1(C_306))), inference(resolution, [status(thm)], [c_630, c_2])).
% 3.30/1.54  tff(c_679, plain, (![A_307]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_307) | ~v5_relat_1('#skF_9', A_307) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_505, c_666])).
% 3.30/1.54  tff(c_689, plain, (![A_307]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_307) | ~v5_relat_1('#skF_9', A_307))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_679])).
% 3.30/1.54  tff(c_534, plain, (![A_275, B_276, C_277]: (r2_hidden(k4_tarski(A_275, '#skF_5'(A_275, B_276, C_277)), C_277) | ~r2_hidden(A_275, k10_relat_1(C_277, B_276)) | ~v1_relat_1(C_277))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_476, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 3.30/1.54  tff(c_62, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_153), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_497, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_153), '#skF_9') | ~m1_subset_1(F_153, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_476, c_62])).
% 3.30/1.54  tff(c_538, plain, (![B_276]: (~r2_hidden('#skF_5'('#skF_10', B_276, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_276, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_276)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_534, c_497])).
% 3.30/1.54  tff(c_742, plain, (![B_314]: (~r2_hidden('#skF_5'('#skF_10', B_314, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_314, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_314)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_538])).
% 3.30/1.54  tff(c_750, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_742])).
% 3.30/1.54  tff(c_756, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_505, c_750])).
% 3.30/1.54  tff(c_759, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_689, c_756])).
% 3.30/1.54  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_759])).
% 3.30/1.54  tff(c_764, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_56])).
% 3.30/1.54  tff(c_798, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_764])).
% 3.30/1.54  tff(c_818, plain, (![A_332, B_333, C_334]: (r2_hidden('#skF_5'(A_332, B_333, C_334), k2_relat_1(C_334)) | ~r2_hidden(A_332, k10_relat_1(C_334, B_333)) | ~v1_relat_1(C_334))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_910, plain, (![A_356, B_357, C_358, A_359]: (r2_hidden('#skF_5'(A_356, B_357, C_358), A_359) | ~v5_relat_1(C_358, A_359) | ~r2_hidden(A_356, k10_relat_1(C_358, B_357)) | ~v1_relat_1(C_358))), inference(resolution, [status(thm)], [c_818, c_30])).
% 3.30/1.54  tff(c_946, plain, (![A_363, B_364, C_365, A_366]: (m1_subset_1('#skF_5'(A_363, B_364, C_365), A_366) | ~v5_relat_1(C_365, A_366) | ~r2_hidden(A_363, k10_relat_1(C_365, B_364)) | ~v1_relat_1(C_365))), inference(resolution, [status(thm)], [c_910, c_2])).
% 3.30/1.54  tff(c_959, plain, (![A_366]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_366) | ~v5_relat_1('#skF_9', A_366) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_798, c_946])).
% 3.30/1.54  tff(c_969, plain, (![A_366]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_366) | ~v5_relat_1('#skF_9', A_366))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_959])).
% 3.30/1.54  tff(c_829, plain, (![A_339, B_340, C_341]: (r2_hidden(k4_tarski(A_339, '#skF_5'(A_339, B_340, C_341)), C_341) | ~r2_hidden(A_339, k10_relat_1(C_341, B_340)) | ~v1_relat_1(C_341))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.54  tff(c_765, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 3.30/1.54  tff(c_54, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_153), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.54  tff(c_826, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_153), '#skF_9') | ~m1_subset_1(F_153, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_765, c_54])).
% 3.30/1.54  tff(c_833, plain, (![B_340]: (~r2_hidden('#skF_5'('#skF_10', B_340, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_340, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_340)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_829, c_826])).
% 3.30/1.54  tff(c_1001, plain, (![B_373]: (~r2_hidden('#skF_5'('#skF_10', B_373, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_373, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_373)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_833])).
% 3.30/1.54  tff(c_1009, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_1001])).
% 3.30/1.54  tff(c_1015, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_798, c_1009])).
% 3.30/1.54  tff(c_1018, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_969, c_1015])).
% 3.30/1.54  tff(c_1022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_1018])).
% 3.30/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  Inference rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Ref     : 0
% 3.30/1.54  #Sup     : 198
% 3.30/1.54  #Fact    : 0
% 3.30/1.54  #Define  : 0
% 3.30/1.54  #Split   : 7
% 3.30/1.54  #Chain   : 0
% 3.30/1.54  #Close   : 0
% 3.30/1.54  
% 3.30/1.54  Ordering : KBO
% 3.30/1.54  
% 3.30/1.54  Simplification rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Subsume      : 11
% 3.30/1.54  #Demod        : 53
% 3.30/1.54  #Tautology    : 20
% 3.30/1.54  #SimpNegUnit  : 3
% 3.30/1.54  #BackRed      : 6
% 3.30/1.54  
% 3.30/1.54  #Partial instantiations: 0
% 3.30/1.54  #Strategies tried      : 1
% 3.30/1.54  
% 3.30/1.54  Timing (in seconds)
% 3.30/1.54  ----------------------
% 3.30/1.54  Preprocessing        : 0.33
% 3.30/1.54  Parsing              : 0.16
% 3.30/1.54  CNF conversion       : 0.03
% 3.30/1.54  Main loop            : 0.39
% 3.30/1.54  Inferencing          : 0.15
% 3.30/1.54  Reduction            : 0.11
% 3.30/1.54  Demodulation         : 0.07
% 3.30/1.54  BG Simplification    : 0.02
% 3.30/1.54  Subsumption          : 0.07
% 3.30/1.54  Abstraction          : 0.02
% 3.30/1.54  MUC search           : 0.00
% 3.30/1.54  Cooper               : 0.00
% 3.30/1.54  Total                : 0.76
% 3.30/1.55  Index Insertion      : 0.00
% 3.30/1.55  Index Deletion       : 0.00
% 3.30/1.55  Index Matching       : 0.00
% 3.30/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
