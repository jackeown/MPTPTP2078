%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:34 EST 2020

% Result     : Theorem 14.73s
% Output     : CNFRefutation 14.73s
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
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_12

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_110,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_40,plain,(
    ! [A_59,B_60] : v1_relat_1(k2_zfmisc_1(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_29445,plain,(
    ! [B_1995,A_1996] :
      ( v1_relat_1(B_1995)
      | ~ m1_subset_1(B_1995,k1_zfmisc_1(A_1996))
      | ~ v1_relat_1(A_1996) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_29451,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_29445])).

tff(c_29455,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_29451])).

tff(c_29630,plain,(
    ! [A_2055,B_2056,C_2057,D_2058] :
      ( k7_relset_1(A_2055,B_2056,C_2057,D_2058) = k9_relat_1(C_2057,D_2058)
      | ~ m1_subset_1(C_2057,k1_zfmisc_1(k2_zfmisc_1(A_2055,B_2056))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_29645,plain,(
    ! [D_2058] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_2058) = k9_relat_1('#skF_10',D_2058) ),
    inference(resolution,[status(thm)],[c_54,c_29630])).

tff(c_102,plain,(
    ! [B_173,A_174] :
      ( v1_relat_1(B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_174))
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_108,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_108])).

tff(c_15688,plain,(
    ! [A_1168,B_1169,C_1170,D_1171] :
      ( k7_relset_1(A_1168,B_1169,C_1170,D_1171) = k9_relat_1(C_1170,D_1171)
      | ~ m1_subset_1(C_1170,k1_zfmisc_1(k2_zfmisc_1(A_1168,B_1169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15707,plain,(
    ! [D_1171] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_1171) = k9_relat_1('#skF_10',D_1171) ),
    inference(resolution,[status(thm)],[c_54,c_15688])).

tff(c_762,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k7_relset_1(A_301,B_302,C_303,D_304) = k9_relat_1(C_303,D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_777,plain,(
    ! [D_304] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_304) = k9_relat_1('#skF_10',D_304) ),
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
    ( r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8'))
    | m1_subset_1('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_89,plain,(
    m1_subset_1('#skF_12','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_68,plain,
    ( r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8'))
    | r2_hidden('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_135,plain,(
    r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_72,plain,
    ( r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8'))
    | r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_171,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_177,plain,(
    ! [B_2] :
      ( r2_hidden(k4_tarski('#skF_12','#skF_11'),B_2)
      | ~ r1_tarski('#skF_10',B_2) ) ),
    inference(resolution,[status(thm)],[c_171,c_2])).

tff(c_395,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k7_relset_1(A_229,B_230,C_231,D_232) = k9_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_414,plain,(
    ! [D_232] : k7_relset_1('#skF_9','#skF_7','#skF_10',D_232) = k9_relat_1('#skF_10',D_232) ),
    inference(resolution,[status(thm)],[c_54,c_395])).

tff(c_62,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | ~ r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_449,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_62])).

tff(c_450,plain,(
    ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_531,plain,(
    ! [D_251,A_252,B_253,E_254] :
      ( r2_hidden(D_251,k9_relat_1(A_252,B_253))
      | ~ r2_hidden(E_254,B_253)
      | ~ r2_hidden(k4_tarski(E_254,D_251),A_252)
      | ~ v1_relat_1(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_577,plain,(
    ! [D_255,A_256] :
      ( r2_hidden(D_255,k9_relat_1(A_256,'#skF_8'))
      | ~ r2_hidden(k4_tarski('#skF_12',D_255),A_256)
      | ~ v1_relat_1(A_256) ) ),
    inference(resolution,[status(thm)],[c_135,c_531])).

tff(c_593,plain,
    ( r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_171,c_577])).

tff(c_604,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_593])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_450,c_604])).

tff(c_616,plain,(
    ! [F_257] :
      ( ~ r2_hidden(F_257,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_257,'#skF_11'),'#skF_10')
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
    r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_780,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_635])).

tff(c_44,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_6'(A_61,B_62,C_63),B_62)
      | ~ r2_hidden(A_61,k9_relat_1(C_63,B_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_871,plain,(
    ! [A_320,B_321,C_322] :
      ( r2_hidden(k4_tarski('#skF_6'(A_320,B_321,C_322),A_320),C_322)
      | ~ r2_hidden(A_320,k9_relat_1(C_322,B_321))
      | ~ v1_relat_1(C_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_636,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | r2_hidden(k4_tarski('#skF_12','#skF_11'),'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_751,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_636,c_70])).

tff(c_877,plain,(
    ! [B_321] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_321,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_321,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_321))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_871,c_751])).

tff(c_1653,plain,(
    ! [B_445] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_445,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_445,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_445)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_877])).

tff(c_1661,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
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
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_2350,plain,(
    ! [A_546,B_547,C_548,B_549] :
      ( r2_hidden(k4_tarski('#skF_6'(A_546,B_547,C_548),A_546),B_549)
      | ~ r1_tarski(C_548,B_549)
      | ~ r2_hidden(A_546,k9_relat_1(C_548,B_547))
      | ~ v1_relat_1(C_548) ) ),
    inference(resolution,[status(thm)],[c_871,c_2])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15013,plain,(
    ! [D_1107,A_1109,C_1110,C_1108,B_1106] :
      ( r2_hidden('#skF_6'(A_1109,B_1106,C_1110),C_1108)
      | ~ r1_tarski(C_1110,k2_zfmisc_1(C_1108,D_1107))
      | ~ r2_hidden(A_1109,k9_relat_1(C_1110,B_1106))
      | ~ v1_relat_1(C_1110) ) ),
    inference(resolution,[status(thm)],[c_2350,c_12])).

tff(c_15074,plain,(
    ! [A_1109,B_1106] :
      ( r2_hidden('#skF_6'(A_1109,B_1106,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1109,k9_relat_1('#skF_10',B_1106))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_88,c_15013])).

tff(c_15100,plain,(
    ! [A_1111,B_1112] :
      ( r2_hidden('#skF_6'(A_1111,B_1112,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1111,k9_relat_1('#skF_10',B_1112)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_15074])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15130,plain,(
    ! [A_1113,B_1114] :
      ( m1_subset_1('#skF_6'(A_1113,B_1114,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1113,k9_relat_1('#skF_10',B_1114)) ) ),
    inference(resolution,[status(thm)],[c_15100,c_14])).

tff(c_15304,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_780,c_15130])).

tff(c_15389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1667,c_15304])).

tff(c_15390,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_15710,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15707,c_15390])).

tff(c_15823,plain,(
    ! [A_1192,B_1193,C_1194] :
      ( r2_hidden(k4_tarski('#skF_6'(A_1192,B_1193,C_1194),A_1192),C_1194)
      | ~ r2_hidden(A_1192,k9_relat_1(C_1194,B_1193))
      | ~ v1_relat_1(C_1194) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_15391,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | r2_hidden('#skF_12','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_15511,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_15391,c_66])).

tff(c_15830,plain,(
    ! [B_1193] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_1193,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_1193,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_1193))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_15823,c_15511])).

tff(c_16772,plain,(
    ! [B_1323] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_1323,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_1323,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_1323)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_15830])).

tff(c_16776,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_16772])).

tff(c_16779,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_15710,c_16776])).

tff(c_18280,plain,(
    ! [A_1471,B_1472,C_1473,B_1474] :
      ( r2_hidden(k4_tarski('#skF_6'(A_1471,B_1472,C_1473),A_1471),B_1474)
      | ~ r1_tarski(C_1473,B_1474)
      | ~ r2_hidden(A_1471,k9_relat_1(C_1473,B_1472))
      | ~ v1_relat_1(C_1473) ) ),
    inference(resolution,[status(thm)],[c_15823,c_2])).

tff(c_29001,plain,(
    ! [A_1985,C_1981,D_1982,C_1983,B_1984] :
      ( r2_hidden('#skF_6'(A_1985,B_1984,C_1981),C_1983)
      | ~ r1_tarski(C_1981,k2_zfmisc_1(C_1983,D_1982))
      | ~ r2_hidden(A_1985,k9_relat_1(C_1981,B_1984))
      | ~ v1_relat_1(C_1981) ) ),
    inference(resolution,[status(thm)],[c_18280,c_12])).

tff(c_29074,plain,(
    ! [A_1985,B_1984] :
      ( r2_hidden('#skF_6'(A_1985,B_1984,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1985,k9_relat_1('#skF_10',B_1984))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_88,c_29001])).

tff(c_29104,plain,(
    ! [A_1986,B_1987] :
      ( r2_hidden('#skF_6'(A_1986,B_1987,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1986,k9_relat_1('#skF_10',B_1987)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_29074])).

tff(c_29134,plain,(
    ! [A_1988,B_1989] :
      ( m1_subset_1('#skF_6'(A_1988,B_1989,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1988,k9_relat_1('#skF_10',B_1989)) ) ),
    inference(resolution,[status(thm)],[c_29104,c_14])).

tff(c_29318,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_15710,c_29134])).

tff(c_29421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16779,c_29318])).

tff(c_29422,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_9','#skF_7','#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_29648,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29645,c_29422])).

tff(c_29767,plain,(
    ! [A_2083,B_2084,C_2085] :
      ( r2_hidden(k4_tarski('#skF_6'(A_2083,B_2084,C_2085),A_2083),C_2085)
      | ~ r2_hidden(A_2083,k9_relat_1(C_2085,B_2084))
      | ~ v1_relat_1(C_2085) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_29423,plain,(
    ~ m1_subset_1('#skF_12','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_74,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9')
      | m1_subset_1('#skF_12','#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_29513,plain,(
    ! [F_159] :
      ( ~ r2_hidden(F_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(F_159,'#skF_11'),'#skF_10')
      | ~ m1_subset_1(F_159,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_29423,c_74])).

tff(c_29780,plain,(
    ! [B_2084] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_2084,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_2084,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_2084))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_29767,c_29513])).

tff(c_30582,plain,(
    ! [B_2206] :
      ( ~ r2_hidden('#skF_6'('#skF_11',B_2206,'#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_6'('#skF_11',B_2206,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10',B_2206)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29455,c_29780])).

tff(c_30590,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_44,c_30582])).

tff(c_30596,plain,(
    ~ m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29455,c_29648,c_30590])).

tff(c_31055,plain,(
    ! [A_2289,B_2290,C_2291,B_2292] :
      ( r2_hidden(k4_tarski('#skF_6'(A_2289,B_2290,C_2291),A_2289),B_2292)
      | ~ r1_tarski(C_2291,B_2292)
      | ~ r2_hidden(A_2289,k9_relat_1(C_2291,B_2290))
      | ~ v1_relat_1(C_2291) ) ),
    inference(resolution,[status(thm)],[c_29767,c_2])).

tff(c_33356,plain,(
    ! [C_2509,D_2506,A_2510,B_2508,C_2507] :
      ( r2_hidden('#skF_6'(A_2510,B_2508,C_2509),C_2507)
      | ~ r1_tarski(C_2509,k2_zfmisc_1(C_2507,D_2506))
      | ~ r2_hidden(A_2510,k9_relat_1(C_2509,B_2508))
      | ~ v1_relat_1(C_2509) ) ),
    inference(resolution,[status(thm)],[c_31055,c_12])).

tff(c_33387,plain,(
    ! [A_2510,B_2508] :
      ( r2_hidden('#skF_6'(A_2510,B_2508,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_2510,k9_relat_1('#skF_10',B_2508))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_88,c_33356])).

tff(c_33442,plain,(
    ! [A_2517,B_2518] :
      ( r2_hidden('#skF_6'(A_2517,B_2518,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_2517,k9_relat_1('#skF_10',B_2518)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29455,c_33387])).

tff(c_33453,plain,(
    ! [A_2519,B_2520] :
      ( m1_subset_1('#skF_6'(A_2519,B_2520,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_2519,k9_relat_1('#skF_10',B_2520)) ) ),
    inference(resolution,[status(thm)],[c_33442,c_14])).

tff(c_33560,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_8','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_29648,c_33453])).

tff(c_33608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30596,c_33560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.73/7.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.73/7.16  
% 14.73/7.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.73/7.16  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1 > #skF_12
% 14.73/7.16  
% 14.73/7.16  %Foreground sorts:
% 14.73/7.16  
% 14.73/7.16  
% 14.73/7.16  %Background operators:
% 14.73/7.16  
% 14.73/7.16  
% 14.73/7.16  %Foreground operators:
% 14.73/7.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.73/7.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.73/7.16  tff('#skF_11', type, '#skF_11': $i).
% 14.73/7.16  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 14.73/7.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.73/7.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.73/7.16  tff('#skF_7', type, '#skF_7': $i).
% 14.73/7.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.73/7.16  tff('#skF_10', type, '#skF_10': $i).
% 14.73/7.16  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 14.73/7.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.73/7.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.73/7.16  tff('#skF_9', type, '#skF_9': $i).
% 14.73/7.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.73/7.16  tff('#skF_8', type, '#skF_8': $i).
% 14.73/7.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.73/7.16  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 14.73/7.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.73/7.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.73/7.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.73/7.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.73/7.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.73/7.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.73/7.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.73/7.16  tff('#skF_12', type, '#skF_12': $i).
% 14.73/7.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.73/7.16  
% 14.73/7.18  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.73/7.18  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 14.73/7.18  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.73/7.18  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 14.73/7.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 14.73/7.18  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 14.73/7.18  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 14.73/7.18  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.73/7.18  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 14.73/7.18  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 14.73/7.18  tff(c_40, plain, (![A_59, B_60]: (v1_relat_1(k2_zfmisc_1(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.73/7.18  tff(c_54, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.18  tff(c_29445, plain, (![B_1995, A_1996]: (v1_relat_1(B_1995) | ~m1_subset_1(B_1995, k1_zfmisc_1(A_1996)) | ~v1_relat_1(A_1996))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.73/7.18  tff(c_29451, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_29445])).
% 14.73/7.18  tff(c_29455, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_29451])).
% 14.73/7.18  tff(c_29630, plain, (![A_2055, B_2056, C_2057, D_2058]: (k7_relset_1(A_2055, B_2056, C_2057, D_2058)=k9_relat_1(C_2057, D_2058) | ~m1_subset_1(C_2057, k1_zfmisc_1(k2_zfmisc_1(A_2055, B_2056))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.73/7.18  tff(c_29645, plain, (![D_2058]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_2058)=k9_relat_1('#skF_10', D_2058))), inference(resolution, [status(thm)], [c_54, c_29630])).
% 14.73/7.18  tff(c_102, plain, (![B_173, A_174]: (v1_relat_1(B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(A_174)) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.73/7.18  tff(c_108, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_102])).
% 14.73/7.18  tff(c_112, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_108])).
% 14.73/7.18  tff(c_15688, plain, (![A_1168, B_1169, C_1170, D_1171]: (k7_relset_1(A_1168, B_1169, C_1170, D_1171)=k9_relat_1(C_1170, D_1171) | ~m1_subset_1(C_1170, k1_zfmisc_1(k2_zfmisc_1(A_1168, B_1169))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.73/7.18  tff(c_15707, plain, (![D_1171]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_1171)=k9_relat_1('#skF_10', D_1171))), inference(resolution, [status(thm)], [c_54, c_15688])).
% 14.73/7.18  tff(c_762, plain, (![A_301, B_302, C_303, D_304]: (k7_relset_1(A_301, B_302, C_303, D_304)=k9_relat_1(C_303, D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.73/7.18  tff(c_777, plain, (![D_304]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_304)=k9_relat_1('#skF_10', D_304))), inference(resolution, [status(thm)], [c_54, c_762])).
% 14.73/7.18  tff(c_91, plain, (![A_170, B_171]: (r2_hidden('#skF_1'(A_170, B_171), A_170) | r1_tarski(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.73/7.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.73/7.18  tff(c_99, plain, (![A_170]: (r1_tarski(A_170, A_170))), inference(resolution, [status(thm)], [c_91, c_4])).
% 14.73/7.18  tff(c_76, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')) | m1_subset_1('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.18  tff(c_89, plain, (m1_subset_1('#skF_12', '#skF_9')), inference(splitLeft, [status(thm)], [c_76])).
% 14.73/7.18  tff(c_68, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')) | r2_hidden('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.18  tff(c_135, plain, (r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 14.73/7.18  tff(c_72, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')) | r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.18  tff(c_171, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(splitLeft, [status(thm)], [c_72])).
% 14.73/7.18  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.73/7.18  tff(c_177, plain, (![B_2]: (r2_hidden(k4_tarski('#skF_12', '#skF_11'), B_2) | ~r1_tarski('#skF_10', B_2))), inference(resolution, [status(thm)], [c_171, c_2])).
% 14.73/7.18  tff(c_395, plain, (![A_229, B_230, C_231, D_232]: (k7_relset_1(A_229, B_230, C_231, D_232)=k9_relat_1(C_231, D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.73/7.18  tff(c_414, plain, (![D_232]: (k7_relset_1('#skF_9', '#skF_7', '#skF_10', D_232)=k9_relat_1('#skF_10', D_232))), inference(resolution, [status(thm)], [c_54, c_395])).
% 14.73/7.18  tff(c_62, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | ~r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.18  tff(c_449, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_62])).
% 14.73/7.18  tff(c_450, plain, (~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(splitLeft, [status(thm)], [c_449])).
% 14.73/7.18  tff(c_531, plain, (![D_251, A_252, B_253, E_254]: (r2_hidden(D_251, k9_relat_1(A_252, B_253)) | ~r2_hidden(E_254, B_253) | ~r2_hidden(k4_tarski(E_254, D_251), A_252) | ~v1_relat_1(A_252))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.73/7.18  tff(c_577, plain, (![D_255, A_256]: (r2_hidden(D_255, k9_relat_1(A_256, '#skF_8')) | ~r2_hidden(k4_tarski('#skF_12', D_255), A_256) | ~v1_relat_1(A_256))), inference(resolution, [status(thm)], [c_135, c_531])).
% 14.73/7.18  tff(c_593, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_171, c_577])).
% 14.73/7.18  tff(c_604, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_593])).
% 14.73/7.18  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_450, c_604])).
% 14.73/7.18  tff(c_616, plain, (![F_257]: (~r2_hidden(F_257, '#skF_8') | ~r2_hidden(k4_tarski(F_257, '#skF_11'), '#skF_10') | ~m1_subset_1(F_257, '#skF_9'))), inference(splitRight, [status(thm)], [c_449])).
% 14.73/7.18  tff(c_624, plain, (~r2_hidden('#skF_12', '#skF_8') | ~m1_subset_1('#skF_12', '#skF_9') | ~r1_tarski('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_177, c_616])).
% 14.73/7.18  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_89, c_135, c_624])).
% 14.73/7.18  tff(c_635, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_72])).
% 14.73/7.18  tff(c_780, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_777, c_635])).
% 14.73/7.18  tff(c_44, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_6'(A_61, B_62, C_63), B_62) | ~r2_hidden(A_61, k9_relat_1(C_63, B_62)) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.73/7.18  tff(c_871, plain, (![A_320, B_321, C_322]: (r2_hidden(k4_tarski('#skF_6'(A_320, B_321, C_322), A_320), C_322) | ~r2_hidden(A_320, k9_relat_1(C_322, B_321)) | ~v1_relat_1(C_322))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.73/7.18  tff(c_636, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_72])).
% 14.73/7.18  tff(c_70, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | r2_hidden(k4_tarski('#skF_12', '#skF_11'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.18  tff(c_751, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_636, c_70])).
% 14.73/7.18  tff(c_877, plain, (![B_321]: (~r2_hidden('#skF_6'('#skF_11', B_321, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_321, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_321)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_871, c_751])).
% 14.73/7.18  tff(c_1653, plain, (![B_445]: (~r2_hidden('#skF_6'('#skF_11', B_445, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_445, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_445)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_877])).
% 14.73/7.18  tff(c_1661, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_44, c_1653])).
% 14.73/7.18  tff(c_1667, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_780, c_1661])).
% 14.73/7.18  tff(c_80, plain, (![A_166, B_167]: (r1_tarski(A_166, B_167) | ~m1_subset_1(A_166, k1_zfmisc_1(B_167)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.73/7.18  tff(c_88, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_80])).
% 14.73/7.18  tff(c_2350, plain, (![A_546, B_547, C_548, B_549]: (r2_hidden(k4_tarski('#skF_6'(A_546, B_547, C_548), A_546), B_549) | ~r1_tarski(C_548, B_549) | ~r2_hidden(A_546, k9_relat_1(C_548, B_547)) | ~v1_relat_1(C_548))), inference(resolution, [status(thm)], [c_871, c_2])).
% 14.73/7.18  tff(c_12, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.73/7.18  tff(c_15013, plain, (![D_1107, A_1109, C_1110, C_1108, B_1106]: (r2_hidden('#skF_6'(A_1109, B_1106, C_1110), C_1108) | ~r1_tarski(C_1110, k2_zfmisc_1(C_1108, D_1107)) | ~r2_hidden(A_1109, k9_relat_1(C_1110, B_1106)) | ~v1_relat_1(C_1110))), inference(resolution, [status(thm)], [c_2350, c_12])).
% 14.73/7.18  tff(c_15074, plain, (![A_1109, B_1106]: (r2_hidden('#skF_6'(A_1109, B_1106, '#skF_10'), '#skF_9') | ~r2_hidden(A_1109, k9_relat_1('#skF_10', B_1106)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_88, c_15013])).
% 14.73/7.18  tff(c_15100, plain, (![A_1111, B_1112]: (r2_hidden('#skF_6'(A_1111, B_1112, '#skF_10'), '#skF_9') | ~r2_hidden(A_1111, k9_relat_1('#skF_10', B_1112)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_15074])).
% 14.73/7.19  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.73/7.19  tff(c_15130, plain, (![A_1113, B_1114]: (m1_subset_1('#skF_6'(A_1113, B_1114, '#skF_10'), '#skF_9') | ~r2_hidden(A_1113, k9_relat_1('#skF_10', B_1114)))), inference(resolution, [status(thm)], [c_15100, c_14])).
% 14.73/7.19  tff(c_15304, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_780, c_15130])).
% 14.73/7.19  tff(c_15389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1667, c_15304])).
% 14.73/7.19  tff(c_15390, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_68])).
% 14.73/7.19  tff(c_15710, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_15707, c_15390])).
% 14.73/7.19  tff(c_15823, plain, (![A_1192, B_1193, C_1194]: (r2_hidden(k4_tarski('#skF_6'(A_1192, B_1193, C_1194), A_1192), C_1194) | ~r2_hidden(A_1192, k9_relat_1(C_1194, B_1193)) | ~v1_relat_1(C_1194))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.73/7.19  tff(c_15391, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 14.73/7.19  tff(c_66, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | r2_hidden('#skF_12', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.19  tff(c_15511, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_15391, c_66])).
% 14.73/7.19  tff(c_15830, plain, (![B_1193]: (~r2_hidden('#skF_6'('#skF_11', B_1193, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_1193, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_1193)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_15823, c_15511])).
% 14.73/7.19  tff(c_16772, plain, (![B_1323]: (~r2_hidden('#skF_6'('#skF_11', B_1323, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_1323, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_1323)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_15830])).
% 14.73/7.19  tff(c_16776, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_44, c_16772])).
% 14.73/7.19  tff(c_16779, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_15710, c_16776])).
% 14.73/7.19  tff(c_18280, plain, (![A_1471, B_1472, C_1473, B_1474]: (r2_hidden(k4_tarski('#skF_6'(A_1471, B_1472, C_1473), A_1471), B_1474) | ~r1_tarski(C_1473, B_1474) | ~r2_hidden(A_1471, k9_relat_1(C_1473, B_1472)) | ~v1_relat_1(C_1473))), inference(resolution, [status(thm)], [c_15823, c_2])).
% 14.73/7.19  tff(c_29001, plain, (![A_1985, C_1981, D_1982, C_1983, B_1984]: (r2_hidden('#skF_6'(A_1985, B_1984, C_1981), C_1983) | ~r1_tarski(C_1981, k2_zfmisc_1(C_1983, D_1982)) | ~r2_hidden(A_1985, k9_relat_1(C_1981, B_1984)) | ~v1_relat_1(C_1981))), inference(resolution, [status(thm)], [c_18280, c_12])).
% 14.73/7.19  tff(c_29074, plain, (![A_1985, B_1984]: (r2_hidden('#skF_6'(A_1985, B_1984, '#skF_10'), '#skF_9') | ~r2_hidden(A_1985, k9_relat_1('#skF_10', B_1984)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_88, c_29001])).
% 14.73/7.19  tff(c_29104, plain, (![A_1986, B_1987]: (r2_hidden('#skF_6'(A_1986, B_1987, '#skF_10'), '#skF_9') | ~r2_hidden(A_1986, k9_relat_1('#skF_10', B_1987)))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_29074])).
% 14.73/7.19  tff(c_29134, plain, (![A_1988, B_1989]: (m1_subset_1('#skF_6'(A_1988, B_1989, '#skF_10'), '#skF_9') | ~r2_hidden(A_1988, k9_relat_1('#skF_10', B_1989)))), inference(resolution, [status(thm)], [c_29104, c_14])).
% 14.73/7.19  tff(c_29318, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_15710, c_29134])).
% 14.73/7.19  tff(c_29421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16779, c_29318])).
% 14.73/7.19  tff(c_29422, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_9', '#skF_7', '#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_76])).
% 14.73/7.19  tff(c_29648, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_29645, c_29422])).
% 14.73/7.19  tff(c_29767, plain, (![A_2083, B_2084, C_2085]: (r2_hidden(k4_tarski('#skF_6'(A_2083, B_2084, C_2085), A_2083), C_2085) | ~r2_hidden(A_2083, k9_relat_1(C_2085, B_2084)) | ~v1_relat_1(C_2085))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.73/7.19  tff(c_29423, plain, (~m1_subset_1('#skF_12', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 14.73/7.19  tff(c_74, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9') | m1_subset_1('#skF_12', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.73/7.19  tff(c_29513, plain, (![F_159]: (~r2_hidden(F_159, '#skF_8') | ~r2_hidden(k4_tarski(F_159, '#skF_11'), '#skF_10') | ~m1_subset_1(F_159, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_29423, c_74])).
% 14.73/7.19  tff(c_29780, plain, (![B_2084]: (~r2_hidden('#skF_6'('#skF_11', B_2084, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_2084, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_2084)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_29767, c_29513])).
% 14.73/7.19  tff(c_30582, plain, (![B_2206]: (~r2_hidden('#skF_6'('#skF_11', B_2206, '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_6'('#skF_11', B_2206, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', B_2206)))), inference(demodulation, [status(thm), theory('equality')], [c_29455, c_29780])).
% 14.73/7.19  tff(c_30590, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_44, c_30582])).
% 14.73/7.19  tff(c_30596, plain, (~m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_29455, c_29648, c_30590])).
% 14.73/7.19  tff(c_31055, plain, (![A_2289, B_2290, C_2291, B_2292]: (r2_hidden(k4_tarski('#skF_6'(A_2289, B_2290, C_2291), A_2289), B_2292) | ~r1_tarski(C_2291, B_2292) | ~r2_hidden(A_2289, k9_relat_1(C_2291, B_2290)) | ~v1_relat_1(C_2291))), inference(resolution, [status(thm)], [c_29767, c_2])).
% 14.73/7.19  tff(c_33356, plain, (![C_2509, D_2506, A_2510, B_2508, C_2507]: (r2_hidden('#skF_6'(A_2510, B_2508, C_2509), C_2507) | ~r1_tarski(C_2509, k2_zfmisc_1(C_2507, D_2506)) | ~r2_hidden(A_2510, k9_relat_1(C_2509, B_2508)) | ~v1_relat_1(C_2509))), inference(resolution, [status(thm)], [c_31055, c_12])).
% 14.73/7.19  tff(c_33387, plain, (![A_2510, B_2508]: (r2_hidden('#skF_6'(A_2510, B_2508, '#skF_10'), '#skF_9') | ~r2_hidden(A_2510, k9_relat_1('#skF_10', B_2508)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_88, c_33356])).
% 14.73/7.19  tff(c_33442, plain, (![A_2517, B_2518]: (r2_hidden('#skF_6'(A_2517, B_2518, '#skF_10'), '#skF_9') | ~r2_hidden(A_2517, k9_relat_1('#skF_10', B_2518)))), inference(demodulation, [status(thm), theory('equality')], [c_29455, c_33387])).
% 14.73/7.19  tff(c_33453, plain, (![A_2519, B_2520]: (m1_subset_1('#skF_6'(A_2519, B_2520, '#skF_10'), '#skF_9') | ~r2_hidden(A_2519, k9_relat_1('#skF_10', B_2520)))), inference(resolution, [status(thm)], [c_33442, c_14])).
% 14.73/7.19  tff(c_33560, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_8', '#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_29648, c_33453])).
% 14.73/7.19  tff(c_33608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30596, c_33560])).
% 14.73/7.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.73/7.19  
% 14.73/7.19  Inference rules
% 14.73/7.19  ----------------------
% 14.73/7.19  #Ref     : 0
% 14.73/7.19  #Sup     : 7421
% 14.73/7.19  #Fact    : 0
% 14.73/7.19  #Define  : 0
% 14.73/7.19  #Split   : 127
% 14.73/7.19  #Chain   : 0
% 14.73/7.19  #Close   : 0
% 14.73/7.19  
% 14.73/7.19  Ordering : KBO
% 14.73/7.19  
% 14.73/7.19  Simplification rules
% 14.73/7.19  ----------------------
% 14.73/7.19  #Subsume      : 749
% 14.73/7.19  #Demod        : 1151
% 14.73/7.19  #Tautology    : 270
% 14.73/7.19  #SimpNegUnit  : 19
% 14.73/7.19  #BackRed      : 21
% 14.73/7.19  
% 14.73/7.19  #Partial instantiations: 0
% 14.73/7.19  #Strategies tried      : 1
% 14.73/7.19  
% 14.73/7.19  Timing (in seconds)
% 14.73/7.19  ----------------------
% 14.73/7.19  Preprocessing        : 0.35
% 14.73/7.19  Parsing              : 0.18
% 14.73/7.19  CNF conversion       : 0.04
% 14.73/7.19  Main loop            : 6.00
% 14.73/7.19  Inferencing          : 1.56
% 14.73/7.19  Reduction            : 1.65
% 14.73/7.19  Demodulation         : 1.08
% 14.73/7.19  BG Simplification    : 0.17
% 14.73/7.19  Subsumption          : 2.15
% 14.73/7.19  Abstraction          : 0.23
% 14.73/7.19  MUC search           : 0.00
% 14.73/7.19  Cooper               : 0.00
% 14.73/7.19  Total                : 6.40
% 14.73/7.19  Index Insertion      : 0.00
% 14.73/7.19  Index Deletion       : 0.00
% 14.73/7.19  Index Matching       : 0.00
% 14.73/7.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
