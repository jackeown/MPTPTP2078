%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:39 EST 2020

% Result     : Theorem 10.49s
% Output     : CNFRefutation 10.64s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 317 expanded)
%              Number of leaves         :   33 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  241 ( 894 expanded)
%              Number of equality atoms :   10 (  31 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
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

tff(c_26,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_11373,plain,(
    ! [A_1010,B_1011,C_1012,D_1013] :
      ( k8_relset_1(A_1010,B_1011,C_1012,D_1013) = k10_relat_1(C_1012,D_1013)
      | ~ m1_subset_1(C_1012,k1_zfmisc_1(k2_zfmisc_1(A_1010,B_1011))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_11380,plain,(
    ! [D_1013] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_1013) = k10_relat_1('#skF_9',D_1013) ),
    inference(resolution,[status(thm)],[c_40,c_11373])).

tff(c_7106,plain,(
    ! [A_717,B_718,C_719,D_720] :
      ( k8_relset_1(A_717,B_718,C_719,D_720) = k10_relat_1(C_719,D_720)
      | ~ m1_subset_1(C_719,k1_zfmisc_1(k2_zfmisc_1(A_717,B_718))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7113,plain,(
    ! [D_720] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_720) = k10_relat_1('#skF_9',D_720) ),
    inference(resolution,[status(thm)],[c_40,c_7106])).

tff(c_2108,plain,(
    ! [A_389,B_390,C_391,D_392] :
      ( k8_relset_1(A_389,B_390,C_391,D_392) = k10_relat_1(C_391,D_392)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2115,plain,(
    ! [D_392] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_392) = k10_relat_1('#skF_9',D_392) ),
    inference(resolution,[status(thm)],[c_40,c_2108])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_83,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_86,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_580,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k8_relset_1(A_229,B_230,C_231,D_232) = k10_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_587,plain,(
    ! [D_232] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_232) = k10_relat_1('#skF_9',D_232) ),
    inference(resolution,[status(thm)],[c_40,c_580])).

tff(c_48,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_442,plain,(
    ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_588,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_442])).

tff(c_16,plain,(
    ! [C_29,A_14,D_32] :
      ( r2_hidden(C_29,k2_relat_1(A_14))
      | ~ r2_hidden(k4_tarski(D_32,C_29),A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_86,c_16])).

tff(c_1582,plain,(
    ! [A_322,C_323,B_324,D_325] :
      ( r2_hidden(A_322,k10_relat_1(C_323,B_324))
      | ~ r2_hidden(D_325,B_324)
      | ~ r2_hidden(k4_tarski(A_322,D_325),C_323)
      | ~ r2_hidden(D_325,k2_relat_1(C_323))
      | ~ v1_relat_1(C_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1716,plain,(
    ! [A_330,C_331] :
      ( r2_hidden(A_330,k10_relat_1(C_331,'#skF_7'))
      | ~ r2_hidden(k4_tarski(A_330,'#skF_11'),C_331)
      | ~ r2_hidden('#skF_11',k2_relat_1(C_331))
      | ~ v1_relat_1(C_331) ) ),
    inference(resolution,[status(thm)],[c_72,c_1582])).

tff(c_1790,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_1716])).

tff(c_1813,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_96,c_1790])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_1813])).

tff(c_1828,plain,(
    ! [F_332] :
      ( ~ r2_hidden(F_332,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_332),'#skF_9')
      | ~ m1_subset_1(F_332,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1835,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_1828])).

tff(c_1842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_1835])).

tff(c_1843,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2120,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2115,c_1843])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_5'(A_35,B_36,C_37),k2_relat_1(C_37))
      | ~ r2_hidden(A_35,k10_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1931,plain,(
    ! [A_354,C_355] :
      ( r2_hidden(k4_tarski('#skF_4'(A_354,k2_relat_1(A_354),C_355),C_355),A_354)
      | ~ r2_hidden(C_355,k2_relat_1(A_354)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5323,plain,(
    ! [A_604,C_605,A_606] :
      ( r2_hidden(k4_tarski('#skF_4'(A_604,k2_relat_1(A_604),C_605),C_605),A_606)
      | ~ m1_subset_1(A_604,k1_zfmisc_1(A_606))
      | ~ r2_hidden(C_605,k2_relat_1(A_604)) ) ),
    inference(resolution,[status(thm)],[c_1931,c_8])).

tff(c_5446,plain,(
    ! [C_607,A_608,A_609] :
      ( r2_hidden(C_607,k2_relat_1(A_608))
      | ~ m1_subset_1(A_609,k1_zfmisc_1(A_608))
      | ~ r2_hidden(C_607,k2_relat_1(A_609)) ) ),
    inference(resolution,[status(thm)],[c_5323,c_16])).

tff(c_5470,plain,(
    ! [C_610] :
      ( r2_hidden(C_610,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_610,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_5446])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1955,plain,(
    ! [C_355,D_4,C_3] :
      ( r2_hidden(C_355,D_4)
      | ~ r2_hidden(C_355,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_1931,c_4])).

tff(c_5576,plain,(
    ! [C_611] :
      ( r2_hidden(C_611,'#skF_8')
      | ~ r2_hidden(C_611,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_5470,c_1955])).

tff(c_5616,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k10_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_5576])).

tff(c_5645,plain,(
    ! [A_613,B_614] :
      ( r2_hidden('#skF_5'(A_613,B_614,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_613,k10_relat_1('#skF_9',B_614)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5616])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5671,plain,(
    ! [A_615,B_616] :
      ( m1_subset_1('#skF_5'(A_615,B_616,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_615,k10_relat_1('#skF_9',B_616)) ) ),
    inference(resolution,[status(thm)],[c_5645,c_10])).

tff(c_5729,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_2120,c_5671])).

tff(c_30,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_5'(A_35,B_36,C_37),B_36)
      | ~ r2_hidden(A_35,k10_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2216,plain,(
    ! [A_409,B_410,C_411] :
      ( r2_hidden(k4_tarski(A_409,'#skF_5'(A_409,B_410,C_411)),C_411)
      | ~ r2_hidden(A_409,k10_relat_1(C_411,B_410))
      | ~ v1_relat_1(C_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1844,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2106,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1844,c_56])).

tff(c_2223,plain,(
    ! [B_410] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_410,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_410,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_410))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2216,c_2106])).

tff(c_6823,plain,(
    ! [B_652] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_652,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_652,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_652)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2223])).

tff(c_6831,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_6823])).

tff(c_6838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2120,c_5729,c_6831])).

tff(c_6839,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_7118,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7113,c_6839])).

tff(c_6931,plain,(
    ! [A_683,C_684] :
      ( r2_hidden(k4_tarski('#skF_4'(A_683,k2_relat_1(A_683),C_684),C_684),A_683)
      | ~ r2_hidden(C_684,k2_relat_1(A_683)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9094,plain,(
    ! [A_872,C_873,A_874] :
      ( r2_hidden(k4_tarski('#skF_4'(A_872,k2_relat_1(A_872),C_873),C_873),A_874)
      | ~ m1_subset_1(A_872,k1_zfmisc_1(A_874))
      | ~ r2_hidden(C_873,k2_relat_1(A_872)) ) ),
    inference(resolution,[status(thm)],[c_6931,c_8])).

tff(c_9197,plain,(
    ! [C_875,A_876,A_877] :
      ( r2_hidden(C_875,k2_relat_1(A_876))
      | ~ m1_subset_1(A_877,k1_zfmisc_1(A_876))
      | ~ r2_hidden(C_875,k2_relat_1(A_877)) ) ),
    inference(resolution,[status(thm)],[c_9094,c_16])).

tff(c_9217,plain,(
    ! [C_878] :
      ( r2_hidden(C_878,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_878,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_9197])).

tff(c_6954,plain,(
    ! [C_684,D_4,C_3] :
      ( r2_hidden(C_684,D_4)
      | ~ r2_hidden(C_684,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_6931,c_4])).

tff(c_9300,plain,(
    ! [C_879] :
      ( r2_hidden(C_879,'#skF_8')
      | ~ r2_hidden(C_879,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_9217,c_6954])).

tff(c_9340,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k10_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_9300])).

tff(c_9369,plain,(
    ! [A_881,B_882] :
      ( r2_hidden('#skF_5'(A_881,B_882,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_881,k10_relat_1('#skF_9',B_882)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_9340])).

tff(c_9392,plain,(
    ! [A_883,B_884] :
      ( m1_subset_1('#skF_5'(A_883,B_884,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_883,k10_relat_1('#skF_9',B_884)) ) ),
    inference(resolution,[status(thm)],[c_9369,c_10])).

tff(c_9450,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_7118,c_9392])).

tff(c_7178,plain,(
    ! [A_725,B_726,C_727] :
      ( r2_hidden(k4_tarski(A_725,'#skF_5'(A_725,B_726,C_727)),C_727)
      | ~ r2_hidden(A_725,k10_relat_1(C_727,B_726))
      | ~ v1_relat_1(C_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6840,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6918,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6840,c_60])).

tff(c_7192,plain,(
    ! [B_726] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_726,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_726,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_726))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_7178,c_6918])).

tff(c_11165,plain,(
    ! [B_953] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_953,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_953,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_953)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_7192])).

tff(c_11173,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_11165])).

tff(c_11180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_7118,c_9450,c_11173])).

tff(c_11181,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11385,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11380,c_11181])).

tff(c_11395,plain,(
    ! [A_1015,B_1016,C_1017] :
      ( r2_hidden(k4_tarski(A_1015,'#skF_5'(A_1015,B_1016,C_1017)),C_1017)
      | ~ r2_hidden(A_1015,k10_relat_1(C_1017,B_1016))
      | ~ v1_relat_1(C_1017) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11182,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_11235,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_11182,c_52])).

tff(c_11409,plain,(
    ! [B_1016] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1016,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1016,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1016))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_11395,c_11235])).

tff(c_11808,plain,(
    ! [B_1056] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1056,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1056,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1056)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_11409])).

tff(c_11812,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_11808])).

tff(c_11815,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_11385,c_11812])).

tff(c_11237,plain,(
    ! [A_981,C_982] :
      ( r2_hidden(k4_tarski('#skF_4'(A_981,k2_relat_1(A_981),C_982),C_982),A_981)
      | ~ r2_hidden(C_982,k2_relat_1(A_981)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14227,plain,(
    ! [A_1225,C_1226,A_1227] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1225,k2_relat_1(A_1225),C_1226),C_1226),A_1227)
      | ~ m1_subset_1(A_1225,k1_zfmisc_1(A_1227))
      | ~ r2_hidden(C_1226,k2_relat_1(A_1225)) ) ),
    inference(resolution,[status(thm)],[c_11237,c_8])).

tff(c_14350,plain,(
    ! [C_1228,A_1229,A_1230] :
      ( r2_hidden(C_1228,k2_relat_1(A_1229))
      | ~ m1_subset_1(A_1230,k1_zfmisc_1(A_1229))
      | ~ r2_hidden(C_1228,k2_relat_1(A_1230)) ) ),
    inference(resolution,[status(thm)],[c_14227,c_16])).

tff(c_14374,plain,(
    ! [C_1231] :
      ( r2_hidden(C_1231,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_1231,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_14350])).

tff(c_11257,plain,(
    ! [C_982,D_4,C_3] :
      ( r2_hidden(C_982,D_4)
      | ~ r2_hidden(C_982,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_11237,c_4])).

tff(c_14469,plain,(
    ! [C_1232] :
      ( r2_hidden(C_1232,'#skF_8')
      | ~ r2_hidden(C_1232,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_14374,c_11257])).

tff(c_14513,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k10_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_14469])).

tff(c_14543,plain,(
    ! [A_1234,B_1235] :
      ( r2_hidden('#skF_5'(A_1234,B_1235,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1234,k10_relat_1('#skF_9',B_1235)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_14513])).

tff(c_14575,plain,(
    ! [A_1236,B_1237] :
      ( m1_subset_1('#skF_5'(A_1236,B_1237,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1236,k10_relat_1('#skF_9',B_1237)) ) ),
    inference(resolution,[status(thm)],[c_14543,c_10])).

tff(c_14610,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_11385,c_14575])).

tff(c_14640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11815,c_14610])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.49/3.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.49/3.66  
% 10.49/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.49/3.66  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 10.49/3.66  
% 10.49/3.66  %Foreground sorts:
% 10.49/3.66  
% 10.49/3.66  
% 10.49/3.66  %Background operators:
% 10.49/3.66  
% 10.49/3.66  
% 10.49/3.66  %Foreground operators:
% 10.49/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.49/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.49/3.66  tff('#skF_11', type, '#skF_11': $i).
% 10.49/3.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.49/3.66  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 10.49/3.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.49/3.66  tff('#skF_7', type, '#skF_7': $i).
% 10.49/3.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.49/3.66  tff('#skF_10', type, '#skF_10': $i).
% 10.49/3.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.49/3.66  tff('#skF_6', type, '#skF_6': $i).
% 10.49/3.66  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.49/3.66  tff('#skF_9', type, '#skF_9': $i).
% 10.49/3.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.49/3.66  tff('#skF_8', type, '#skF_8': $i).
% 10.49/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.49/3.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.49/3.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.49/3.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.49/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.49/3.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.49/3.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.49/3.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.49/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.49/3.66  
% 10.64/3.68  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.64/3.68  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 10.64/3.68  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.64/3.68  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 10.64/3.68  tff(f_57, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 10.64/3.68  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 10.64/3.68  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 10.64/3.68  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.64/3.68  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 10.64/3.68  tff(c_26, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.64/3.68  tff(c_40, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_65, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.64/3.68  tff(c_68, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_65])).
% 10.64/3.68  tff(c_71, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 10.64/3.68  tff(c_11373, plain, (![A_1010, B_1011, C_1012, D_1013]: (k8_relset_1(A_1010, B_1011, C_1012, D_1013)=k10_relat_1(C_1012, D_1013) | ~m1_subset_1(C_1012, k1_zfmisc_1(k2_zfmisc_1(A_1010, B_1011))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.64/3.68  tff(c_11380, plain, (![D_1013]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_1013)=k10_relat_1('#skF_9', D_1013))), inference(resolution, [status(thm)], [c_40, c_11373])).
% 10.64/3.68  tff(c_7106, plain, (![A_717, B_718, C_719, D_720]: (k8_relset_1(A_717, B_718, C_719, D_720)=k10_relat_1(C_719, D_720) | ~m1_subset_1(C_719, k1_zfmisc_1(k2_zfmisc_1(A_717, B_718))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.64/3.68  tff(c_7113, plain, (![D_720]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_720)=k10_relat_1('#skF_9', D_720))), inference(resolution, [status(thm)], [c_40, c_7106])).
% 10.64/3.68  tff(c_2108, plain, (![A_389, B_390, C_391, D_392]: (k8_relset_1(A_389, B_390, C_391, D_392)=k10_relat_1(C_391, D_392) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.64/3.68  tff(c_2115, plain, (![D_392]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_392)=k10_relat_1('#skF_9', D_392))), inference(resolution, [status(thm)], [c_40, c_2108])).
% 10.64/3.68  tff(c_62, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_83, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_62])).
% 10.64/3.68  tff(c_54, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_72, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 10.64/3.68  tff(c_58, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_86, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_58])).
% 10.64/3.68  tff(c_580, plain, (![A_229, B_230, C_231, D_232]: (k8_relset_1(A_229, B_230, C_231, D_232)=k10_relat_1(C_231, D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.64/3.68  tff(c_587, plain, (![D_232]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_232)=k10_relat_1('#skF_9', D_232))), inference(resolution, [status(thm)], [c_40, c_580])).
% 10.64/3.68  tff(c_48, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_442, plain, (~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_48])).
% 10.64/3.68  tff(c_588, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_587, c_442])).
% 10.64/3.68  tff(c_16, plain, (![C_29, A_14, D_32]: (r2_hidden(C_29, k2_relat_1(A_14)) | ~r2_hidden(k4_tarski(D_32, C_29), A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.64/3.68  tff(c_96, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_86, c_16])).
% 10.64/3.68  tff(c_1582, plain, (![A_322, C_323, B_324, D_325]: (r2_hidden(A_322, k10_relat_1(C_323, B_324)) | ~r2_hidden(D_325, B_324) | ~r2_hidden(k4_tarski(A_322, D_325), C_323) | ~r2_hidden(D_325, k2_relat_1(C_323)) | ~v1_relat_1(C_323))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.64/3.68  tff(c_1716, plain, (![A_330, C_331]: (r2_hidden(A_330, k10_relat_1(C_331, '#skF_7')) | ~r2_hidden(k4_tarski(A_330, '#skF_11'), C_331) | ~r2_hidden('#skF_11', k2_relat_1(C_331)) | ~v1_relat_1(C_331))), inference(resolution, [status(thm)], [c_72, c_1582])).
% 10.64/3.68  tff(c_1790, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_11', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_86, c_1716])).
% 10.64/3.68  tff(c_1813, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_96, c_1790])).
% 10.64/3.68  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_1813])).
% 10.64/3.68  tff(c_1828, plain, (![F_332]: (~r2_hidden(F_332, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_332), '#skF_9') | ~m1_subset_1(F_332, '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 10.64/3.68  tff(c_1835, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_86, c_1828])).
% 10.64/3.68  tff(c_1842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_1835])).
% 10.64/3.68  tff(c_1843, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 10.64/3.68  tff(c_2120, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2115, c_1843])).
% 10.64/3.68  tff(c_34, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_5'(A_35, B_36, C_37), k2_relat_1(C_37)) | ~r2_hidden(A_35, k10_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.64/3.68  tff(c_1931, plain, (![A_354, C_355]: (r2_hidden(k4_tarski('#skF_4'(A_354, k2_relat_1(A_354), C_355), C_355), A_354) | ~r2_hidden(C_355, k2_relat_1(A_354)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.64/3.68  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.64/3.68  tff(c_5323, plain, (![A_604, C_605, A_606]: (r2_hidden(k4_tarski('#skF_4'(A_604, k2_relat_1(A_604), C_605), C_605), A_606) | ~m1_subset_1(A_604, k1_zfmisc_1(A_606)) | ~r2_hidden(C_605, k2_relat_1(A_604)))), inference(resolution, [status(thm)], [c_1931, c_8])).
% 10.64/3.68  tff(c_5446, plain, (![C_607, A_608, A_609]: (r2_hidden(C_607, k2_relat_1(A_608)) | ~m1_subset_1(A_609, k1_zfmisc_1(A_608)) | ~r2_hidden(C_607, k2_relat_1(A_609)))), inference(resolution, [status(thm)], [c_5323, c_16])).
% 10.64/3.68  tff(c_5470, plain, (![C_610]: (r2_hidden(C_610, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_610, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_40, c_5446])).
% 10.64/3.68  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.64/3.68  tff(c_1955, plain, (![C_355, D_4, C_3]: (r2_hidden(C_355, D_4) | ~r2_hidden(C_355, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_1931, c_4])).
% 10.64/3.68  tff(c_5576, plain, (![C_611]: (r2_hidden(C_611, '#skF_8') | ~r2_hidden(C_611, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_5470, c_1955])).
% 10.64/3.68  tff(c_5616, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k10_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_5576])).
% 10.64/3.68  tff(c_5645, plain, (![A_613, B_614]: (r2_hidden('#skF_5'(A_613, B_614, '#skF_9'), '#skF_8') | ~r2_hidden(A_613, k10_relat_1('#skF_9', B_614)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_5616])).
% 10.64/3.68  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.64/3.68  tff(c_5671, plain, (![A_615, B_616]: (m1_subset_1('#skF_5'(A_615, B_616, '#skF_9'), '#skF_8') | ~r2_hidden(A_615, k10_relat_1('#skF_9', B_616)))), inference(resolution, [status(thm)], [c_5645, c_10])).
% 10.64/3.68  tff(c_5729, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_2120, c_5671])).
% 10.64/3.68  tff(c_30, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_5'(A_35, B_36, C_37), B_36) | ~r2_hidden(A_35, k10_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.64/3.68  tff(c_2216, plain, (![A_409, B_410, C_411]: (r2_hidden(k4_tarski(A_409, '#skF_5'(A_409, B_410, C_411)), C_411) | ~r2_hidden(A_409, k10_relat_1(C_411, B_410)) | ~v1_relat_1(C_411))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.64/3.68  tff(c_1844, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_58])).
% 10.64/3.68  tff(c_56, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_2106, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1844, c_56])).
% 10.64/3.68  tff(c_2223, plain, (![B_410]: (~r2_hidden('#skF_5'('#skF_10', B_410, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_410, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_410)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_2216, c_2106])).
% 10.64/3.68  tff(c_6823, plain, (![B_652]: (~r2_hidden('#skF_5'('#skF_10', B_652, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_652, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_652)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2223])).
% 10.64/3.68  tff(c_6831, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_6823])).
% 10.64/3.68  tff(c_6838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_2120, c_5729, c_6831])).
% 10.64/3.68  tff(c_6839, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 10.64/3.68  tff(c_7118, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_7113, c_6839])).
% 10.64/3.68  tff(c_6931, plain, (![A_683, C_684]: (r2_hidden(k4_tarski('#skF_4'(A_683, k2_relat_1(A_683), C_684), C_684), A_683) | ~r2_hidden(C_684, k2_relat_1(A_683)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.64/3.68  tff(c_9094, plain, (![A_872, C_873, A_874]: (r2_hidden(k4_tarski('#skF_4'(A_872, k2_relat_1(A_872), C_873), C_873), A_874) | ~m1_subset_1(A_872, k1_zfmisc_1(A_874)) | ~r2_hidden(C_873, k2_relat_1(A_872)))), inference(resolution, [status(thm)], [c_6931, c_8])).
% 10.64/3.68  tff(c_9197, plain, (![C_875, A_876, A_877]: (r2_hidden(C_875, k2_relat_1(A_876)) | ~m1_subset_1(A_877, k1_zfmisc_1(A_876)) | ~r2_hidden(C_875, k2_relat_1(A_877)))), inference(resolution, [status(thm)], [c_9094, c_16])).
% 10.64/3.68  tff(c_9217, plain, (![C_878]: (r2_hidden(C_878, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_878, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_40, c_9197])).
% 10.64/3.68  tff(c_6954, plain, (![C_684, D_4, C_3]: (r2_hidden(C_684, D_4) | ~r2_hidden(C_684, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_6931, c_4])).
% 10.64/3.68  tff(c_9300, plain, (![C_879]: (r2_hidden(C_879, '#skF_8') | ~r2_hidden(C_879, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_9217, c_6954])).
% 10.64/3.68  tff(c_9340, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k10_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_9300])).
% 10.64/3.68  tff(c_9369, plain, (![A_881, B_882]: (r2_hidden('#skF_5'(A_881, B_882, '#skF_9'), '#skF_8') | ~r2_hidden(A_881, k10_relat_1('#skF_9', B_882)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_9340])).
% 10.64/3.68  tff(c_9392, plain, (![A_883, B_884]: (m1_subset_1('#skF_5'(A_883, B_884, '#skF_9'), '#skF_8') | ~r2_hidden(A_883, k10_relat_1('#skF_9', B_884)))), inference(resolution, [status(thm)], [c_9369, c_10])).
% 10.64/3.68  tff(c_9450, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_7118, c_9392])).
% 10.64/3.68  tff(c_7178, plain, (![A_725, B_726, C_727]: (r2_hidden(k4_tarski(A_725, '#skF_5'(A_725, B_726, C_727)), C_727) | ~r2_hidden(A_725, k10_relat_1(C_727, B_726)) | ~v1_relat_1(C_727))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.64/3.68  tff(c_6840, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_62])).
% 10.64/3.68  tff(c_60, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_6918, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_6840, c_60])).
% 10.64/3.68  tff(c_7192, plain, (![B_726]: (~r2_hidden('#skF_5'('#skF_10', B_726, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_726, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_726)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_7178, c_6918])).
% 10.64/3.68  tff(c_11165, plain, (![B_953]: (~r2_hidden('#skF_5'('#skF_10', B_953, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_953, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_953)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_7192])).
% 10.64/3.68  tff(c_11173, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_11165])).
% 10.64/3.68  tff(c_11180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_7118, c_9450, c_11173])).
% 10.64/3.68  tff(c_11181, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 10.64/3.68  tff(c_11385, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11380, c_11181])).
% 10.64/3.68  tff(c_11395, plain, (![A_1015, B_1016, C_1017]: (r2_hidden(k4_tarski(A_1015, '#skF_5'(A_1015, B_1016, C_1017)), C_1017) | ~r2_hidden(A_1015, k10_relat_1(C_1017, B_1016)) | ~v1_relat_1(C_1017))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.64/3.68  tff(c_11182, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 10.64/3.68  tff(c_52, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.64/3.68  tff(c_11235, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_11182, c_52])).
% 10.64/3.68  tff(c_11409, plain, (![B_1016]: (~r2_hidden('#skF_5'('#skF_10', B_1016, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1016, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1016)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_11395, c_11235])).
% 10.64/3.68  tff(c_11808, plain, (![B_1056]: (~r2_hidden('#skF_5'('#skF_10', B_1056, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1056, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1056)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_11409])).
% 10.64/3.68  tff(c_11812, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_11808])).
% 10.64/3.68  tff(c_11815, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_11385, c_11812])).
% 10.64/3.68  tff(c_11237, plain, (![A_981, C_982]: (r2_hidden(k4_tarski('#skF_4'(A_981, k2_relat_1(A_981), C_982), C_982), A_981) | ~r2_hidden(C_982, k2_relat_1(A_981)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.64/3.68  tff(c_14227, plain, (![A_1225, C_1226, A_1227]: (r2_hidden(k4_tarski('#skF_4'(A_1225, k2_relat_1(A_1225), C_1226), C_1226), A_1227) | ~m1_subset_1(A_1225, k1_zfmisc_1(A_1227)) | ~r2_hidden(C_1226, k2_relat_1(A_1225)))), inference(resolution, [status(thm)], [c_11237, c_8])).
% 10.64/3.68  tff(c_14350, plain, (![C_1228, A_1229, A_1230]: (r2_hidden(C_1228, k2_relat_1(A_1229)) | ~m1_subset_1(A_1230, k1_zfmisc_1(A_1229)) | ~r2_hidden(C_1228, k2_relat_1(A_1230)))), inference(resolution, [status(thm)], [c_14227, c_16])).
% 10.64/3.68  tff(c_14374, plain, (![C_1231]: (r2_hidden(C_1231, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_1231, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_40, c_14350])).
% 10.64/3.68  tff(c_11257, plain, (![C_982, D_4, C_3]: (r2_hidden(C_982, D_4) | ~r2_hidden(C_982, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_11237, c_4])).
% 10.64/3.68  tff(c_14469, plain, (![C_1232]: (r2_hidden(C_1232, '#skF_8') | ~r2_hidden(C_1232, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_14374, c_11257])).
% 10.64/3.68  tff(c_14513, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k10_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_14469])).
% 10.64/3.68  tff(c_14543, plain, (![A_1234, B_1235]: (r2_hidden('#skF_5'(A_1234, B_1235, '#skF_9'), '#skF_8') | ~r2_hidden(A_1234, k10_relat_1('#skF_9', B_1235)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_14513])).
% 10.64/3.68  tff(c_14575, plain, (![A_1236, B_1237]: (m1_subset_1('#skF_5'(A_1236, B_1237, '#skF_9'), '#skF_8') | ~r2_hidden(A_1236, k10_relat_1('#skF_9', B_1237)))), inference(resolution, [status(thm)], [c_14543, c_10])).
% 10.64/3.68  tff(c_14610, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_11385, c_14575])).
% 10.64/3.68  tff(c_14640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11815, c_14610])).
% 10.64/3.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.64/3.68  
% 10.64/3.68  Inference rules
% 10.64/3.68  ----------------------
% 10.64/3.68  #Ref     : 0
% 10.64/3.68  #Sup     : 3692
% 10.64/3.68  #Fact    : 0
% 10.64/3.68  #Define  : 0
% 10.64/3.68  #Split   : 14
% 10.64/3.68  #Chain   : 0
% 10.64/3.68  #Close   : 0
% 10.64/3.68  
% 10.64/3.68  Ordering : KBO
% 10.64/3.68  
% 10.64/3.68  Simplification rules
% 10.64/3.68  ----------------------
% 10.64/3.68  #Subsume      : 172
% 10.64/3.68  #Demod        : 158
% 10.64/3.68  #Tautology    : 96
% 10.64/3.68  #SimpNegUnit  : 14
% 10.64/3.68  #BackRed      : 40
% 10.64/3.68  
% 10.64/3.68  #Partial instantiations: 0
% 10.64/3.68  #Strategies tried      : 1
% 10.64/3.68  
% 10.64/3.68  Timing (in seconds)
% 10.64/3.68  ----------------------
% 10.64/3.68  Preprocessing        : 0.35
% 10.64/3.68  Parsing              : 0.18
% 10.64/3.68  CNF conversion       : 0.04
% 10.64/3.68  Main loop            : 2.48
% 10.64/3.68  Inferencing          : 0.70
% 10.64/3.68  Reduction            : 0.62
% 10.64/3.68  Demodulation         : 0.41
% 10.64/3.68  BG Simplification    : 0.10
% 10.64/3.68  Subsumption          : 0.80
% 10.64/3.68  Abstraction          : 0.12
% 10.64/3.68  MUC search           : 0.00
% 10.64/3.68  Cooper               : 0.00
% 10.64/3.68  Total                : 2.87
% 10.64/3.68  Index Insertion      : 0.00
% 10.64/3.68  Index Deletion       : 0.00
% 10.64/3.68  Index Matching       : 0.00
% 10.64/3.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
