%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:38 EST 2020

% Result     : Theorem 17.62s
% Output     : CNFRefutation 17.62s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 311 expanded)
%              Number of leaves         :   36 ( 119 expanded)
%              Depth                    :    8
%              Number of atoms          :  240 ( 875 expanded)
%              Number of equality atoms :   10 (  25 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_110,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_46,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_40,plain,(
    ! [A_59,B_60] : v1_relat_1(k2_zfmisc_1(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30863,plain,(
    ! [B_2004,A_2005] :
      ( v1_relat_1(B_2004)
      | ~ m1_subset_1(B_2004,k1_zfmisc_1(A_2005))
      | ~ v1_relat_1(A_2005) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30869,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_54,c_30863])).

tff(c_30873,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30869])).

tff(c_31014,plain,(
    ! [A_2058,B_2059,C_2060,D_2061] :
      ( k8_relset_1(A_2058,B_2059,C_2060,D_2061) = k10_relat_1(C_2060,D_2061)
      | ~ m1_subset_1(C_2060,k1_zfmisc_1(k2_zfmisc_1(A_2058,B_2059))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_31029,plain,(
    ! [D_2061] : k8_relset_1('#skF_7','#skF_9','#skF_10',D_2061) = k10_relat_1('#skF_10',D_2061) ),
    inference(resolution,[status(thm)],[c_54,c_31014])).

tff(c_102,plain,(
    ! [B_173,A_174] :
      ( v1_relat_1(B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_174))
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_108,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_108])).

tff(c_15864,plain,(
    ! [A_1156,B_1157,C_1158,D_1159] :
      ( k8_relset_1(A_1156,B_1157,C_1158,D_1159) = k10_relat_1(C_1158,D_1159)
      | ~ m1_subset_1(C_1158,k1_zfmisc_1(k2_zfmisc_1(A_1156,B_1157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15883,plain,(
    ! [D_1159] : k8_relset_1('#skF_7','#skF_9','#skF_10',D_1159) = k10_relat_1('#skF_10',D_1159) ),
    inference(resolution,[status(thm)],[c_54,c_15864])).

tff(c_762,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k8_relset_1(A_301,B_302,C_303,D_304) = k10_relat_1(C_303,D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_777,plain,(
    ! [D_304] : k8_relset_1('#skF_7','#skF_9','#skF_10',D_304) = k10_relat_1('#skF_10',D_304) ),
    inference(resolution,[status(thm)],[c_54,c_762])).

tff(c_91,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_1'(A_170,B_171),A_170)
      | r1_tarski(A_170,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_170] : r1_tarski(A_170,A_170) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_76,plain,
    ( r2_hidden('#skF_11',k8_relset_1('#skF_7','#skF_9','#skF_10','#skF_8'))
    | m1_subset_1('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_89,plain,(
    m1_subset_1('#skF_12','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_68,plain,
    ( r2_hidden('#skF_11',k8_relset_1('#skF_7','#skF_9','#skF_10','#skF_8'))
    | r2_hidden('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_135,plain,(
    r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_72,plain,
    ( r2_hidden('#skF_11',k8_relset_1('#skF_7','#skF_9','#skF_10','#skF_8'))
    | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_171,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_177,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_11','#skF_12'),B_2)
      | ~ r1_tarski('#skF_10',B_2) ) ),
    inference(resolution,[status(thm)],[c_171,c_2])).

tff(c_395,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k8_relset_1(A_229,B_230,C_231,D_232) = k10_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_414,plain,(
    ! [D_232] : k8_relset_1('#skF_7','#skF_9','#skF_10',D_232) = k10_relat_1('#skF_10',D_232) ),
    inference(resolution,[status(thm)],[c_54,c_395])).

tff(c_62,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | ~ r2_hidden('#skF_11',k8_relset_1('#skF_7','#skF_9','#skF_10','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_449,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_62])).

tff(c_450,plain,(
    ~ r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_531,plain,(
    ! [D_251,A_252,B_253,E_254] :
      ( r2_hidden(D_251,k10_relat_1(A_252,B_253))
      | ~ r2_hidden(E_254,B_253)
      | ~ r2_hidden(k4_tarski(D_251,E_254),A_252)
      | ~ v1_relat_1(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_577,plain,(
    ! [D_255,A_256] :
      ( r2_hidden(D_255,k10_relat_1(A_256,'#skF_8'))
      | ~ r2_hidden(k4_tarski(D_255,'#skF_12'),A_256)
      | ~ v1_relat_1(A_256) ) ),
    inference(resolution,[status(thm)],[c_135,c_531])).

tff(c_593,plain,
    ( r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_171,c_577])).

tff(c_604,plain,(
    r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_593])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_450,c_604])).

tff(c_616,plain,(
    ! [F_257] :
      ( ~ r2_hidden(F_257,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_257),'#skF_10')
      | ~ m1_subset_1(F_257,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_624,plain,
    ( ~ r2_hidden('#skF_12','#skF_8')
    | ~ m1_subset_1('#skF_12','#skF_9')
    | ~ r1_tarski('#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_177,c_616])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_89,c_135,c_624])).

tff(c_635,plain,(
    r2_hidden('#skF_11',k8_relset_1('#skF_7','#skF_9','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_780,plain,(
    r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_635])).

tff(c_44,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_6'(A_61,B_62,C_63),B_62)
      | ~ r2_hidden(A_61,k10_relat_1(C_63,B_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_871,plain,(
    ! [A_320,B_321,C_322] :
      ( r2_hidden(k4_tarski(A_320,'#skF_6'(A_320,B_321,C_322)),C_322)
      | ~ r2_hidden(A_320,k10_relat_1(C_322,B_321))
      | ~ v1_relat_1(C_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_636,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_751,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_636,c_70])).

tff(c_877,plain,(
    ! [B_321] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_321,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_321,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_321))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_871,c_751])).

tff(c_1653,plain,(
    ! [B_445] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_445,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_445,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_445)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_877])).

tff(c_1661,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_1653])).

tff(c_1667,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_780,c_1661])).

tff(c_80,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(A_166,B_167)
      | ~ m1_subset_1(A_166,k1_zfmisc_1(B_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_2350,plain,(
    ! [A_546,B_547,C_548,B_549] :
      ( r2_hidden(k4_tarski(A_546,'#skF_6'(A_546,B_547,C_548)),B_549)
      | ~ r1_tarski(C_548,B_549)
      | ~ r2_hidden(A_546,k10_relat_1(C_548,B_547))
      | ~ v1_relat_1(C_548) ) ),
    inference(resolution,[status(thm)],[c_871,c_2])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15203,plain,(
    ! [B_1094,C_1098,D_1095,C_1096,A_1097] :
      ( r2_hidden('#skF_6'(A_1097,B_1094,C_1098),D_1095)
      | ~ r1_tarski(C_1098,k2_zfmisc_1(C_1096,D_1095))
      | ~ r2_hidden(A_1097,k10_relat_1(C_1098,B_1094))
      | ~ v1_relat_1(C_1098) ) ),
    inference(resolution,[status(thm)],[c_2350,c_10])).

tff(c_15261,plain,(
    ! [A_1097,B_1094] :
      ( r2_hidden('#skF_6'(A_1097,B_1094,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1097,k10_relat_1('#skF_10',B_1094))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_88,c_15203])).

tff(c_15286,plain,(
    ! [A_1099,B_1100] :
      ( r2_hidden('#skF_6'(A_1099,B_1100,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1099,k10_relat_1('#skF_10',B_1100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_15261])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15316,plain,(
    ! [A_1101,B_1102] :
      ( m1_subset_1('#skF_6'(A_1101,B_1102,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1101,k10_relat_1('#skF_10',B_1102)) ) ),
    inference(resolution,[status(thm)],[c_15286,c_14])).

tff(c_15482,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_780,c_15316])).

tff(c_15565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1667,c_15482])).

tff(c_15566,plain,(
    r2_hidden('#skF_11',k8_relset_1('#skF_7','#skF_9','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_15886,plain,(
    r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15883,c_15566])).

tff(c_15999,plain,(
    ! [A_1180,B_1181,C_1182] :
      ( r2_hidden(k4_tarski(A_1180,'#skF_6'(A_1180,B_1181,C_1182)),C_1182)
      | ~ r2_hidden(A_1180,k10_relat_1(C_1182,B_1181))
      | ~ v1_relat_1(C_1182) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_15567,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | r2_hidden('#skF_12','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_15677,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_15567,c_66])).

tff(c_16006,plain,(
    ! [B_1181] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_1181,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_1181,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_1181))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_15999,c_15677])).

tff(c_16948,plain,(
    ! [B_1311] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_1311,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_1311,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_1311)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_16006])).

tff(c_16952,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_16948])).

tff(c_16955,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_15886,c_16952])).

tff(c_18454,plain,(
    ! [A_1459,B_1460,C_1461,B_1462] :
      ( r2_hidden(k4_tarski(A_1459,'#skF_6'(A_1459,B_1460,C_1461)),B_1462)
      | ~ r1_tarski(C_1461,B_1462)
      | ~ r2_hidden(A_1459,k10_relat_1(C_1461,B_1460))
      | ~ v1_relat_1(C_1461) ) ),
    inference(resolution,[status(thm)],[c_15999,c_2])).

tff(c_30406,plain,(
    ! [C_1997,D_1996,C_1998,A_1994,B_1995] :
      ( r2_hidden('#skF_6'(A_1994,B_1995,C_1997),D_1996)
      | ~ r1_tarski(C_1997,k2_zfmisc_1(C_1998,D_1996))
      | ~ r2_hidden(A_1994,k10_relat_1(C_1997,B_1995))
      | ~ v1_relat_1(C_1997) ) ),
    inference(resolution,[status(thm)],[c_18454,c_10])).

tff(c_30479,plain,(
    ! [A_1994,B_1995] :
      ( r2_hidden('#skF_6'(A_1994,B_1995,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1994,k10_relat_1('#skF_10',B_1995))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_88,c_30406])).

tff(c_30509,plain,(
    ! [A_1999,B_2000] :
      ( r2_hidden('#skF_6'(A_1999,B_2000,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1999,k10_relat_1('#skF_10',B_2000)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_30479])).

tff(c_30564,plain,(
    ! [A_2002,B_2003] :
      ( m1_subset_1('#skF_6'(A_2002,B_2003,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_2002,k10_relat_1('#skF_10',B_2003)) ) ),
    inference(resolution,[status(thm)],[c_30509,c_14])).

tff(c_30752,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_15886,c_30564])).

tff(c_30856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16955,c_30752])).

tff(c_30857,plain,(
    r2_hidden('#skF_11',k8_relset_1('#skF_7','#skF_9','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_31032,plain,(
    r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31029,c_30857])).

tff(c_31096,plain,(
    ! [A_2074,B_2075,C_2076] :
      ( r2_hidden(k4_tarski(A_2074,'#skF_6'(A_2074,B_2075,C_2076)),C_2076)
      | ~ r2_hidden(A_2074,k10_relat_1(C_2076,B_2075))
      | ~ v1_relat_1(C_2076) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30858,plain,(
    ~ m1_subset_1('#skF_12','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_74,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | m1_subset_1('#skF_12','#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30986,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski('#skF_11',F_159),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30858,c_74])).

tff(c_31103,plain,(
    ! [B_2075] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_2075,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_2075,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_2075))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_31096,c_30986])).

tff(c_31633,plain,(
    ! [B_2163] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_2163,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_2163,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_2163)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30873,c_31103])).

tff(c_31641,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_31633])).

tff(c_31647,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30873,c_31032,c_31641])).

tff(c_32117,plain,(
    ! [A_2237,B_2238,C_2239,B_2240] :
      ( r2_hidden(k4_tarski(A_2237,'#skF_6'(A_2237,B_2238,C_2239)),B_2240)
      | ~ r1_tarski(C_2239,B_2240)
      | ~ r2_hidden(A_2237,k10_relat_1(C_2239,B_2238))
      | ~ v1_relat_1(C_2239) ) ),
    inference(resolution,[status(thm)],[c_31096,c_2])).

tff(c_44716,plain,(
    ! [D_2802,C_2803,B_2804,C_2806,A_2805] :
      ( r2_hidden('#skF_6'(A_2805,B_2804,C_2806),D_2802)
      | ~ r1_tarski(C_2806,k2_zfmisc_1(C_2803,D_2802))
      | ~ r2_hidden(A_2805,k10_relat_1(C_2806,B_2804))
      | ~ v1_relat_1(C_2806) ) ),
    inference(resolution,[status(thm)],[c_32117,c_10])).

tff(c_44780,plain,(
    ! [A_2805,B_2804] :
      ( r2_hidden('#skF_6'(A_2805,B_2804,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_2805,k10_relat_1('#skF_10',B_2804))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_88,c_44716])).

tff(c_44807,plain,(
    ! [A_2807,B_2808] :
      ( r2_hidden('#skF_6'(A_2807,B_2808,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_2807,k10_relat_1('#skF_10',B_2808)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30873,c_44780])).

tff(c_44861,plain,(
    ! [A_2809,B_2810] :
      ( m1_subset_1('#skF_6'(A_2809,B_2810,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_2809,k10_relat_1('#skF_10',B_2810)) ) ),
    inference(resolution,[status(thm)],[c_44807,c_14])).

tff(c_45003,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_31032,c_44861])).

tff(c_45062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31647,c_45003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.62/9.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.62/9.21  
% 17.62/9.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.62/9.21  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_12
% 17.62/9.21  
% 17.62/9.21  %Foreground sorts:
% 17.62/9.21  
% 17.62/9.21  
% 17.62/9.21  %Background operators:
% 17.62/9.21  
% 17.62/9.21  
% 17.62/9.21  %Foreground operators:
% 17.62/9.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.62/9.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.62/9.21  tff('#skF_11', type, '#skF_11': $i).
% 17.62/9.21  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 17.62/9.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.62/9.21  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 17.62/9.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.62/9.21  tff('#skF_7', type, '#skF_7': $i).
% 17.62/9.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.62/9.21  tff('#skF_10', type, '#skF_10': $i).
% 17.62/9.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.62/9.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.62/9.21  tff('#skF_9', type, '#skF_9': $i).
% 17.62/9.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.62/9.21  tff('#skF_8', type, '#skF_8': $i).
% 17.62/9.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.62/9.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 17.62/9.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 17.62/9.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.62/9.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.62/9.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.62/9.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.62/9.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.62/9.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.62/9.21  tff('#skF_12', type, '#skF_12': $i).
% 17.62/9.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.62/9.21  
% 17.62/9.23  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 17.62/9.23  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 17.62/9.23  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 17.62/9.23  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 17.62/9.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.62/9.23  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 17.62/9.23  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 17.62/9.23  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 17.62/9.23  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 17.62/9.23  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 17.62/9.23  tff(c_40, plain, (![A_59, B_60]: (v1_relat_1(k2_zfmisc_1(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.62/9.23  tff(c_54, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_30863, plain, (![B_2004, A_2005]: (v1_relat_1(B_2004) | ~m1_subset_1(B_2004, k1_zfmisc_1(A_2005)) | ~v1_relat_1(A_2005))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.62/9.23  tff(c_30869, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_54, c_30863])).
% 17.62/9.23  tff(c_30873, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30869])).
% 17.62/9.23  tff(c_31014, plain, (![A_2058, B_2059, C_2060, D_2061]: (k8_relset_1(A_2058, B_2059, C_2060, D_2061)=k10_relat_1(C_2060, D_2061) | ~m1_subset_1(C_2060, k1_zfmisc_1(k2_zfmisc_1(A_2058, B_2059))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.62/9.23  tff(c_31029, plain, (![D_2061]: (k8_relset_1('#skF_7', '#skF_9', '#skF_10', D_2061)=k10_relat_1('#skF_10', D_2061))), inference(resolution, [status(thm)], [c_54, c_31014])).
% 17.62/9.23  tff(c_102, plain, (![B_173, A_174]: (v1_relat_1(B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(A_174)) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.62/9.23  tff(c_108, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_54, c_102])).
% 17.62/9.23  tff(c_112, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_108])).
% 17.62/9.23  tff(c_15864, plain, (![A_1156, B_1157, C_1158, D_1159]: (k8_relset_1(A_1156, B_1157, C_1158, D_1159)=k10_relat_1(C_1158, D_1159) | ~m1_subset_1(C_1158, k1_zfmisc_1(k2_zfmisc_1(A_1156, B_1157))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.62/9.23  tff(c_15883, plain, (![D_1159]: (k8_relset_1('#skF_7', '#skF_9', '#skF_10', D_1159)=k10_relat_1('#skF_10', D_1159))), inference(resolution, [status(thm)], [c_54, c_15864])).
% 17.62/9.23  tff(c_762, plain, (![A_301, B_302, C_303, D_304]: (k8_relset_1(A_301, B_302, C_303, D_304)=k10_relat_1(C_303, D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.62/9.23  tff(c_777, plain, (![D_304]: (k8_relset_1('#skF_7', '#skF_9', '#skF_10', D_304)=k10_relat_1('#skF_10', D_304))), inference(resolution, [status(thm)], [c_54, c_762])).
% 17.62/9.23  tff(c_91, plain, (![A_170, B_171]: (r2_hidden('#skF_1'(A_170, B_171), A_170) | r1_tarski(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.62/9.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.62/9.23  tff(c_99, plain, (![A_170]: (r1_tarski(A_170, A_170))), inference(resolution, [status(thm)], [c_91, c_4])).
% 17.62/9.23  tff(c_76, plain, (r2_hidden('#skF_11', k8_relset_1('#skF_7', '#skF_9', '#skF_10', '#skF_8')) | m1_subset_1('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_89, plain, (m1_subset_1('#skF_12', '#skF_9')), inference(splitLeft, [status(thm)], [c_76])).
% 17.62/9.23  tff(c_68, plain, (r2_hidden('#skF_11', k8_relset_1('#skF_7', '#skF_9', '#skF_10', '#skF_8')) | r2_hidden('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_135, plain, (r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 17.62/9.23  tff(c_72, plain, (r2_hidden('#skF_11', k8_relset_1('#skF_7', '#skF_9', '#skF_10', '#skF_8')) | r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_171, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(splitLeft, [status(thm)], [c_72])).
% 17.62/9.23  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.62/9.23  tff(c_177, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_11', '#skF_12'), B_2) | ~r1_tarski('#skF_10', B_2))), inference(resolution, [status(thm)], [c_171, c_2])).
% 17.62/9.23  tff(c_395, plain, (![A_229, B_230, C_231, D_232]: (k8_relset_1(A_229, B_230, C_231, D_232)=k10_relat_1(C_231, D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 17.62/9.23  tff(c_414, plain, (![D_232]: (k8_relset_1('#skF_7', '#skF_9', '#skF_10', D_232)=k10_relat_1('#skF_10', D_232))), inference(resolution, [status(thm)], [c_54, c_395])).
% 17.62/9.23  tff(c_62, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | ~r2_hidden('#skF_11', k8_relset_1('#skF_7', '#skF_9', '#skF_10', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_449, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_62])).
% 17.62/9.23  tff(c_450, plain, (~r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8'))), inference(splitLeft, [status(thm)], [c_449])).
% 17.62/9.23  tff(c_531, plain, (![D_251, A_252, B_253, E_254]: (r2_hidden(D_251, k10_relat_1(A_252, B_253)) | ~r2_hidden(E_254, B_253) | ~r2_hidden(k4_tarski(D_251, E_254), A_252) | ~v1_relat_1(A_252))), inference(cnfTransformation, [status(thm)], [f_66])).
% 17.62/9.23  tff(c_577, plain, (![D_255, A_256]: (r2_hidden(D_255, k10_relat_1(A_256, '#skF_8')) | ~r2_hidden(k4_tarski(D_255, '#skF_12'), A_256) | ~v1_relat_1(A_256))), inference(resolution, [status(thm)], [c_135, c_531])).
% 17.62/9.23  tff(c_593, plain, (r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_171, c_577])).
% 17.62/9.23  tff(c_604, plain, (r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_593])).
% 17.62/9.23  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_450, c_604])).
% 17.62/9.23  tff(c_616, plain, (![F_257]: (~r2_hidden(F_257, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_257), '#skF_10') | ~m1_subset_1(F_257, '#skF_9'))), inference(splitRight, [status(thm)], [c_449])).
% 17.62/9.23  tff(c_624, plain, (~r2_hidden('#skF_12', '#skF_8') | ~m1_subset_1('#skF_12', '#skF_9') | ~r1_tarski('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_177, c_616])).
% 17.62/9.23  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_89, c_135, c_624])).
% 17.62/9.23  tff(c_635, plain, (r2_hidden('#skF_11', k8_relset_1('#skF_7', '#skF_9', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_72])).
% 17.62/9.23  tff(c_780, plain, (r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_777, c_635])).
% 17.62/9.23  tff(c_44, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_6'(A_61, B_62, C_63), B_62) | ~r2_hidden(A_61, k10_relat_1(C_63, B_62)) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.62/9.23  tff(c_871, plain, (![A_320, B_321, C_322]: (r2_hidden(k4_tarski(A_320, '#skF_6'(A_320, B_321, C_322)), C_322) | ~r2_hidden(A_320, k10_relat_1(C_322, B_321)) | ~v1_relat_1(C_322))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.62/9.23  tff(c_636, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(splitRight, [status(thm)], [c_72])).
% 17.62/9.23  tff(c_70, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_751, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_636, c_70])).
% 17.62/9.23  tff(c_877, plain, (![B_321]: (~r2_hidden('#skF_6'('#skF_11', B_321, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_321, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_321)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_871, c_751])).
% 17.62/9.23  tff(c_1653, plain, (![B_445]: (~r2_hidden('#skF_6'('#skF_11', B_445, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_445, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_445)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_877])).
% 17.62/9.23  tff(c_1661, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_44, c_1653])).
% 17.62/9.23  tff(c_1667, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_780, c_1661])).
% 17.62/9.23  tff(c_80, plain, (![A_166, B_167]: (r1_tarski(A_166, B_167) | ~m1_subset_1(A_166, k1_zfmisc_1(B_167)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.62/9.23  tff(c_88, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_54, c_80])).
% 17.62/9.23  tff(c_2350, plain, (![A_546, B_547, C_548, B_549]: (r2_hidden(k4_tarski(A_546, '#skF_6'(A_546, B_547, C_548)), B_549) | ~r1_tarski(C_548, B_549) | ~r2_hidden(A_546, k10_relat_1(C_548, B_547)) | ~v1_relat_1(C_548))), inference(resolution, [status(thm)], [c_871, c_2])).
% 17.62/9.23  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.62/9.23  tff(c_15203, plain, (![B_1094, C_1098, D_1095, C_1096, A_1097]: (r2_hidden('#skF_6'(A_1097, B_1094, C_1098), D_1095) | ~r1_tarski(C_1098, k2_zfmisc_1(C_1096, D_1095)) | ~r2_hidden(A_1097, k10_relat_1(C_1098, B_1094)) | ~v1_relat_1(C_1098))), inference(resolution, [status(thm)], [c_2350, c_10])).
% 17.62/9.23  tff(c_15261, plain, (![A_1097, B_1094]: (r2_hidden('#skF_6'(A_1097, B_1094, '#skF_10'), '#skF_9') | ~r2_hidden(A_1097, k10_relat_1('#skF_10', B_1094)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_88, c_15203])).
% 17.62/9.23  tff(c_15286, plain, (![A_1099, B_1100]: (r2_hidden('#skF_6'(A_1099, B_1100, '#skF_10'), '#skF_9') | ~r2_hidden(A_1099, k10_relat_1('#skF_10', B_1100)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_15261])).
% 17.62/9.23  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.62/9.23  tff(c_15316, plain, (![A_1101, B_1102]: (m1_subset_1('#skF_6'(A_1101, B_1102, '#skF_10'), '#skF_9') | ~r2_hidden(A_1101, k10_relat_1('#skF_10', B_1102)))), inference(resolution, [status(thm)], [c_15286, c_14])).
% 17.62/9.23  tff(c_15482, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_780, c_15316])).
% 17.62/9.23  tff(c_15565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1667, c_15482])).
% 17.62/9.23  tff(c_15566, plain, (r2_hidden('#skF_11', k8_relset_1('#skF_7', '#skF_9', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_68])).
% 17.62/9.23  tff(c_15886, plain, (r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_15883, c_15566])).
% 17.62/9.23  tff(c_15999, plain, (![A_1180, B_1181, C_1182]: (r2_hidden(k4_tarski(A_1180, '#skF_6'(A_1180, B_1181, C_1182)), C_1182) | ~r2_hidden(A_1180, k10_relat_1(C_1182, B_1181)) | ~v1_relat_1(C_1182))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.62/9.23  tff(c_15567, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 17.62/9.23  tff(c_66, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | r2_hidden('#skF_12', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_15677, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_15567, c_66])).
% 17.62/9.23  tff(c_16006, plain, (![B_1181]: (~r2_hidden('#skF_6'('#skF_11', B_1181, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_1181, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_1181)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_15999, c_15677])).
% 17.62/9.23  tff(c_16948, plain, (![B_1311]: (~r2_hidden('#skF_6'('#skF_11', B_1311, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_1311, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_1311)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_16006])).
% 17.62/9.23  tff(c_16952, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_44, c_16948])).
% 17.62/9.23  tff(c_16955, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_15886, c_16952])).
% 17.62/9.23  tff(c_18454, plain, (![A_1459, B_1460, C_1461, B_1462]: (r2_hidden(k4_tarski(A_1459, '#skF_6'(A_1459, B_1460, C_1461)), B_1462) | ~r1_tarski(C_1461, B_1462) | ~r2_hidden(A_1459, k10_relat_1(C_1461, B_1460)) | ~v1_relat_1(C_1461))), inference(resolution, [status(thm)], [c_15999, c_2])).
% 17.62/9.23  tff(c_30406, plain, (![C_1997, D_1996, C_1998, A_1994, B_1995]: (r2_hidden('#skF_6'(A_1994, B_1995, C_1997), D_1996) | ~r1_tarski(C_1997, k2_zfmisc_1(C_1998, D_1996)) | ~r2_hidden(A_1994, k10_relat_1(C_1997, B_1995)) | ~v1_relat_1(C_1997))), inference(resolution, [status(thm)], [c_18454, c_10])).
% 17.62/9.23  tff(c_30479, plain, (![A_1994, B_1995]: (r2_hidden('#skF_6'(A_1994, B_1995, '#skF_10'), '#skF_9') | ~r2_hidden(A_1994, k10_relat_1('#skF_10', B_1995)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_88, c_30406])).
% 17.62/9.23  tff(c_30509, plain, (![A_1999, B_2000]: (r2_hidden('#skF_6'(A_1999, B_2000, '#skF_10'), '#skF_9') | ~r2_hidden(A_1999, k10_relat_1('#skF_10', B_2000)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_30479])).
% 17.62/9.23  tff(c_30564, plain, (![A_2002, B_2003]: (m1_subset_1('#skF_6'(A_2002, B_2003, '#skF_10'), '#skF_9') | ~r2_hidden(A_2002, k10_relat_1('#skF_10', B_2003)))), inference(resolution, [status(thm)], [c_30509, c_14])).
% 17.62/9.23  tff(c_30752, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_15886, c_30564])).
% 17.62/9.23  tff(c_30856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16955, c_30752])).
% 17.62/9.23  tff(c_30857, plain, (r2_hidden('#skF_11', k8_relset_1('#skF_7', '#skF_9', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_76])).
% 17.62/9.23  tff(c_31032, plain, (r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_31029, c_30857])).
% 17.62/9.23  tff(c_31096, plain, (![A_2074, B_2075, C_2076]: (r2_hidden(k4_tarski(A_2074, '#skF_6'(A_2074, B_2075, C_2076)), C_2076) | ~r2_hidden(A_2074, k10_relat_1(C_2076, B_2075)) | ~v1_relat_1(C_2076))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.62/9.23  tff(c_30858, plain, (~m1_subset_1('#skF_12', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 17.62/9.23  tff(c_74, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | m1_subset_1('#skF_12', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 17.62/9.23  tff(c_30986, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski('#skF_11', F_159), '#skF_10') | ~m1_subset_1(F_159, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_30858, c_74])).
% 17.62/9.23  tff(c_31103, plain, (![B_2075]: (~r2_hidden('#skF_6'('#skF_11', B_2075, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_2075, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_2075)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_31096, c_30986])).
% 17.62/9.23  tff(c_31633, plain, (![B_2163]: (~r2_hidden('#skF_6'('#skF_11', B_2163, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_2163, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_2163)))), inference(demodulation, [status(thm), theory('equality')], [c_30873, c_31103])).
% 17.62/9.23  tff(c_31641, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_44, c_31633])).
% 17.62/9.23  tff(c_31647, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_30873, c_31032, c_31641])).
% 17.62/9.23  tff(c_32117, plain, (![A_2237, B_2238, C_2239, B_2240]: (r2_hidden(k4_tarski(A_2237, '#skF_6'(A_2237, B_2238, C_2239)), B_2240) | ~r1_tarski(C_2239, B_2240) | ~r2_hidden(A_2237, k10_relat_1(C_2239, B_2238)) | ~v1_relat_1(C_2239))), inference(resolution, [status(thm)], [c_31096, c_2])).
% 17.62/9.23  tff(c_44716, plain, (![D_2802, C_2803, B_2804, C_2806, A_2805]: (r2_hidden('#skF_6'(A_2805, B_2804, C_2806), D_2802) | ~r1_tarski(C_2806, k2_zfmisc_1(C_2803, D_2802)) | ~r2_hidden(A_2805, k10_relat_1(C_2806, B_2804)) | ~v1_relat_1(C_2806))), inference(resolution, [status(thm)], [c_32117, c_10])).
% 17.62/9.23  tff(c_44780, plain, (![A_2805, B_2804]: (r2_hidden('#skF_6'(A_2805, B_2804, '#skF_10'), '#skF_9') | ~r2_hidden(A_2805, k10_relat_1('#skF_10', B_2804)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_88, c_44716])).
% 17.62/9.23  tff(c_44807, plain, (![A_2807, B_2808]: (r2_hidden('#skF_6'(A_2807, B_2808, '#skF_10'), '#skF_9') | ~r2_hidden(A_2807, k10_relat_1('#skF_10', B_2808)))), inference(demodulation, [status(thm), theory('equality')], [c_30873, c_44780])).
% 17.62/9.23  tff(c_44861, plain, (![A_2809, B_2810]: (m1_subset_1('#skF_6'(A_2809, B_2810, '#skF_10'), '#skF_9') | ~r2_hidden(A_2809, k10_relat_1('#skF_10', B_2810)))), inference(resolution, [status(thm)], [c_44807, c_14])).
% 17.62/9.23  tff(c_45003, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_31032, c_44861])).
% 17.62/9.23  tff(c_45062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31647, c_45003])).
% 17.62/9.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.62/9.23  
% 17.62/9.23  Inference rules
% 17.62/9.23  ----------------------
% 17.62/9.23  #Ref     : 0
% 17.62/9.23  #Sup     : 10132
% 17.62/9.23  #Fact    : 2
% 17.62/9.23  #Define  : 0
% 17.62/9.23  #Split   : 153
% 17.62/9.23  #Chain   : 0
% 17.62/9.23  #Close   : 0
% 17.62/9.23  
% 17.62/9.23  Ordering : KBO
% 17.62/9.23  
% 17.62/9.23  Simplification rules
% 17.62/9.23  ----------------------
% 17.62/9.23  #Subsume      : 1694
% 17.62/9.23  #Demod        : 1532
% 17.62/9.23  #Tautology    : 375
% 17.62/9.23  #SimpNegUnit  : 159
% 17.62/9.23  #BackRed      : 119
% 17.62/9.23  
% 17.62/9.23  #Partial instantiations: 0
% 17.62/9.23  #Strategies tried      : 1
% 17.62/9.23  
% 17.62/9.23  Timing (in seconds)
% 17.62/9.23  ----------------------
% 17.62/9.23  Preprocessing        : 0.41
% 17.62/9.23  Parsing              : 0.20
% 17.62/9.24  CNF conversion       : 0.05
% 17.62/9.24  Main loop            : 7.96
% 17.62/9.24  Inferencing          : 1.92
% 17.62/9.24  Reduction            : 2.18
% 17.62/9.24  Demodulation         : 1.44
% 17.62/9.24  BG Simplification    : 0.22
% 17.62/9.24  Subsumption          : 2.99
% 17.62/9.24  Abstraction          : 0.30
% 17.62/9.24  MUC search           : 0.00
% 17.62/9.24  Cooper               : 0.00
% 17.62/9.24  Total                : 8.42
% 17.62/9.24  Index Insertion      : 0.00
% 17.62/9.24  Index Deletion       : 0.00
% 17.62/9.24  Index Matching       : 0.00
% 17.62/9.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
