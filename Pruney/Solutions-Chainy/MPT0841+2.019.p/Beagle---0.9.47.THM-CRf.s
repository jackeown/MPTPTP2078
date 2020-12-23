%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:35 EST 2020

% Result     : Theorem 9.93s
% Output     : CNFRefutation 10.02s
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
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
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

tff(c_26,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_11013,plain,(
    ! [A_1022,B_1023,C_1024,D_1025] :
      ( k7_relset_1(A_1022,B_1023,C_1024,D_1025) = k9_relat_1(C_1024,D_1025)
      | ~ m1_subset_1(C_1024,k1_zfmisc_1(k2_zfmisc_1(A_1022,B_1023))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_11020,plain,(
    ! [D_1025] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_1025) = k9_relat_1('#skF_9',D_1025) ),
    inference(resolution,[status(thm)],[c_40,c_11013])).

tff(c_6473,plain,(
    ! [A_703,B_704,C_705,D_706] :
      ( k7_relset_1(A_703,B_704,C_705,D_706) = k9_relat_1(C_705,D_706)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(A_703,B_704))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6480,plain,(
    ! [D_706] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_706) = k9_relat_1('#skF_9',D_706) ),
    inference(resolution,[status(thm)],[c_40,c_6473])).

tff(c_1871,plain,(
    ! [A_371,B_372,C_373,D_374] :
      ( k7_relset_1(A_371,B_372,C_373,D_374) = k9_relat_1(C_373,D_374)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1878,plain,(
    ! [D_374] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_374) = k9_relat_1('#skF_9',D_374) ),
    inference(resolution,[status(thm)],[c_40,c_1871])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_83,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_86,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_580,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k7_relset_1(A_229,B_230,C_231,D_232) = k9_relat_1(C_231,D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_587,plain,(
    ! [D_232] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_232) = k9_relat_1('#skF_9',D_232) ),
    inference(resolution,[status(thm)],[c_40,c_580])).

tff(c_48,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_442,plain,(
    ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_588,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_442])).

tff(c_16,plain,(
    ! [C_29,A_14,D_32] :
      ( r2_hidden(C_29,k1_relat_1(A_14))
      | ~ r2_hidden(k4_tarski(C_29,D_32),A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_86,c_16])).

tff(c_1373,plain,(
    ! [A_305,C_306,B_307,D_308] :
      ( r2_hidden(A_305,k9_relat_1(C_306,B_307))
      | ~ r2_hidden(D_308,B_307)
      | ~ r2_hidden(k4_tarski(D_308,A_305),C_306)
      | ~ r2_hidden(D_308,k1_relat_1(C_306))
      | ~ v1_relat_1(C_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1484,plain,(
    ! [A_312,C_313] :
      ( r2_hidden(A_312,k9_relat_1(C_313,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',A_312),C_313)
      | ~ r2_hidden('#skF_11',k1_relat_1(C_313))
      | ~ v1_relat_1(C_313) ) ),
    inference(resolution,[status(thm)],[c_72,c_1373])).

tff(c_1554,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_1484])).

tff(c_1576,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_96,c_1554])).

tff(c_1578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_1576])).

tff(c_1591,plain,(
    ! [F_314] :
      ( ~ r2_hidden(F_314,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_314,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_314,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1598,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_1591])).

tff(c_1605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_1598])).

tff(c_1606,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1883,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_1606])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_5'(A_35,B_36,C_37),k1_relat_1(C_37))
      | ~ r2_hidden(A_35,k9_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1694,plain,(
    ! [C_336,A_337] :
      ( r2_hidden(k4_tarski(C_336,'#skF_4'(A_337,k1_relat_1(A_337),C_336)),A_337)
      | ~ r2_hidden(C_336,k1_relat_1(A_337)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5703,plain,(
    ! [C_619,A_620,A_621] :
      ( r2_hidden(k4_tarski(C_619,'#skF_4'(A_620,k1_relat_1(A_620),C_619)),A_621)
      | ~ m1_subset_1(A_620,k1_zfmisc_1(A_621))
      | ~ r2_hidden(C_619,k1_relat_1(A_620)) ) ),
    inference(resolution,[status(thm)],[c_1694,c_8])).

tff(c_5840,plain,(
    ! [C_622,A_623,A_624] :
      ( r2_hidden(C_622,k1_relat_1(A_623))
      | ~ m1_subset_1(A_624,k1_zfmisc_1(A_623))
      | ~ r2_hidden(C_622,k1_relat_1(A_624)) ) ),
    inference(resolution,[status(thm)],[c_5703,c_16])).

tff(c_5864,plain,(
    ! [C_625] :
      ( r2_hidden(C_625,k1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ r2_hidden(C_625,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_5840])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1717,plain,(
    ! [C_336,C_3,D_4] :
      ( r2_hidden(C_336,C_3)
      | ~ r2_hidden(C_336,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_1694,c_6])).

tff(c_5982,plain,(
    ! [C_626] :
      ( r2_hidden(C_626,'#skF_8')
      | ~ r2_hidden(C_626,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_5864,c_1717])).

tff(c_6026,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k9_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_5982])).

tff(c_6056,plain,(
    ! [A_628,B_629] :
      ( r2_hidden('#skF_5'(A_628,B_629,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_628,k9_relat_1('#skF_9',B_629)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6026])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6082,plain,(
    ! [A_630,B_631] :
      ( m1_subset_1('#skF_5'(A_630,B_631,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_630,k9_relat_1('#skF_9',B_631)) ) ),
    inference(resolution,[status(thm)],[c_6056,c_10])).

tff(c_6145,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1883,c_6082])).

tff(c_30,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_5'(A_35,B_36,C_37),B_36)
      | ~ r2_hidden(A_35,k9_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1979,plain,(
    ! [A_391,B_392,C_393] :
      ( r2_hidden(k4_tarski('#skF_5'(A_391,B_392,C_393),A_391),C_393)
      | ~ r2_hidden(A_391,k9_relat_1(C_393,B_392))
      | ~ v1_relat_1(C_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1607,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1869,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1607,c_56])).

tff(c_1986,plain,(
    ! [B_392] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_392,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_392,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_392))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1979,c_1869])).

tff(c_6190,plain,(
    ! [B_638] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_638,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_638,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_638)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1986])).

tff(c_6198,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_6190])).

tff(c_6205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1883,c_6145,c_6198])).

tff(c_6206,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6485,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6480,c_6206])).

tff(c_6298,plain,(
    ! [C_669,A_670] :
      ( r2_hidden(k4_tarski(C_669,'#skF_4'(A_670,k1_relat_1(A_670),C_669)),A_670)
      | ~ r2_hidden(C_669,k1_relat_1(A_670)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9999,plain,(
    ! [C_938,A_939,A_940] :
      ( r2_hidden(k4_tarski(C_938,'#skF_4'(A_939,k1_relat_1(A_939),C_938)),A_940)
      | ~ m1_subset_1(A_939,k1_zfmisc_1(A_940))
      | ~ r2_hidden(C_938,k1_relat_1(A_939)) ) ),
    inference(resolution,[status(thm)],[c_6298,c_8])).

tff(c_10129,plain,(
    ! [C_941,A_942,A_943] :
      ( r2_hidden(C_941,k1_relat_1(A_942))
      | ~ m1_subset_1(A_943,k1_zfmisc_1(A_942))
      | ~ r2_hidden(C_941,k1_relat_1(A_943)) ) ),
    inference(resolution,[status(thm)],[c_9999,c_16])).

tff(c_10149,plain,(
    ! [C_944] :
      ( r2_hidden(C_944,k1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ r2_hidden(C_944,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_10129])).

tff(c_6322,plain,(
    ! [C_669,C_3,D_4] :
      ( r2_hidden(C_669,C_3)
      | ~ r2_hidden(C_669,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_6298,c_6])).

tff(c_10260,plain,(
    ! [C_945] :
      ( r2_hidden(C_945,'#skF_8')
      | ~ r2_hidden(C_945,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_10149,c_6322])).

tff(c_10304,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k9_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_10260])).

tff(c_10334,plain,(
    ! [A_947,B_948] :
      ( r2_hidden('#skF_5'(A_947,B_948,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_947,k9_relat_1('#skF_9',B_948)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_10304])).

tff(c_10360,plain,(
    ! [A_949,B_950] :
      ( m1_subset_1('#skF_5'(A_949,B_950,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_949,k9_relat_1('#skF_9',B_950)) ) ),
    inference(resolution,[status(thm)],[c_10334,c_10])).

tff(c_10423,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6485,c_10360])).

tff(c_6545,plain,(
    ! [A_711,B_712,C_713] :
      ( r2_hidden(k4_tarski('#skF_5'(A_711,B_712,C_713),A_711),C_713)
      | ~ r2_hidden(A_711,k9_relat_1(C_713,B_712))
      | ~ v1_relat_1(C_713) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6207,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6285,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6207,c_60])).

tff(c_6559,plain,(
    ! [B_712] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_712,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_712,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_712))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6545,c_6285])).

tff(c_10805,plain,(
    ! [B_965] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_965,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_965,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_965)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6559])).

tff(c_10813,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_10805])).

tff(c_10820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6485,c_10423,c_10813])).

tff(c_10821,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11025,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11020,c_10821])).

tff(c_11035,plain,(
    ! [A_1027,B_1028,C_1029] :
      ( r2_hidden(k4_tarski('#skF_5'(A_1027,B_1028,C_1029),A_1027),C_1029)
      | ~ r2_hidden(A_1027,k9_relat_1(C_1029,B_1028))
      | ~ v1_relat_1(C_1029) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10822,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10875,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10822,c_52])).

tff(c_11049,plain,(
    ! [B_1028] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1028,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1028,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_1028))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_11035,c_10875])).

tff(c_11448,plain,(
    ! [B_1068] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1068,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1068,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_1068)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_11049])).

tff(c_11452,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_11448])).

tff(c_11455,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_11025,c_11452])).

tff(c_10877,plain,(
    ! [C_993,A_994] :
      ( r2_hidden(k4_tarski(C_993,'#skF_4'(A_994,k1_relat_1(A_994),C_993)),A_994)
      | ~ r2_hidden(C_993,k1_relat_1(A_994)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13867,plain,(
    ! [C_1237,A_1238,A_1239] :
      ( r2_hidden(k4_tarski(C_1237,'#skF_4'(A_1238,k1_relat_1(A_1238),C_1237)),A_1239)
      | ~ m1_subset_1(A_1238,k1_zfmisc_1(A_1239))
      | ~ r2_hidden(C_1237,k1_relat_1(A_1238)) ) ),
    inference(resolution,[status(thm)],[c_10877,c_8])).

tff(c_13990,plain,(
    ! [C_1240,A_1241,A_1242] :
      ( r2_hidden(C_1240,k1_relat_1(A_1241))
      | ~ m1_subset_1(A_1242,k1_zfmisc_1(A_1241))
      | ~ r2_hidden(C_1240,k1_relat_1(A_1242)) ) ),
    inference(resolution,[status(thm)],[c_13867,c_16])).

tff(c_14014,plain,(
    ! [C_1243] :
      ( r2_hidden(C_1243,k1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ r2_hidden(C_1243,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_13990])).

tff(c_10898,plain,(
    ! [C_993,C_3,D_4] :
      ( r2_hidden(C_993,C_3)
      | ~ r2_hidden(C_993,k1_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_10877,c_6])).

tff(c_14109,plain,(
    ! [C_1244] :
      ( r2_hidden(C_1244,'#skF_8')
      | ~ r2_hidden(C_1244,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_14014,c_10898])).

tff(c_14153,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k9_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_14109])).

tff(c_14183,plain,(
    ! [A_1246,B_1247] :
      ( r2_hidden('#skF_5'(A_1246,B_1247,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1246,k9_relat_1('#skF_9',B_1247)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_14153])).

tff(c_14215,plain,(
    ! [A_1248,B_1249] :
      ( m1_subset_1('#skF_5'(A_1248,B_1249,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1248,k9_relat_1('#skF_9',B_1249)) ) ),
    inference(resolution,[status(thm)],[c_14183,c_10])).

tff(c_14250,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_11025,c_14215])).

tff(c_14280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11455,c_14250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.93/3.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.02/3.43  
% 10.02/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.02/3.44  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 10.02/3.44  
% 10.02/3.44  %Foreground sorts:
% 10.02/3.44  
% 10.02/3.44  
% 10.02/3.44  %Background operators:
% 10.02/3.44  
% 10.02/3.44  
% 10.02/3.44  %Foreground operators:
% 10.02/3.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.02/3.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.02/3.44  tff('#skF_11', type, '#skF_11': $i).
% 10.02/3.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.02/3.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.02/3.44  tff('#skF_7', type, '#skF_7': $i).
% 10.02/3.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.02/3.44  tff('#skF_10', type, '#skF_10': $i).
% 10.02/3.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 10.02/3.44  tff('#skF_6', type, '#skF_6': $i).
% 10.02/3.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.02/3.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.02/3.44  tff('#skF_9', type, '#skF_9': $i).
% 10.02/3.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.02/3.44  tff('#skF_8', type, '#skF_8': $i).
% 10.02/3.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.02/3.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.02/3.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.02/3.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.02/3.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.02/3.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.02/3.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.02/3.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.02/3.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.02/3.44  
% 10.02/3.46  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.02/3.46  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 10.02/3.46  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.02/3.46  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 10.02/3.46  tff(f_57, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 10.02/3.46  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 10.02/3.46  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.02/3.46  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 10.02/3.46  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 10.02/3.46  tff(c_26, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.02/3.46  tff(c_40, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_65, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.02/3.46  tff(c_68, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_65])).
% 10.02/3.46  tff(c_71, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 10.02/3.46  tff(c_11013, plain, (![A_1022, B_1023, C_1024, D_1025]: (k7_relset_1(A_1022, B_1023, C_1024, D_1025)=k9_relat_1(C_1024, D_1025) | ~m1_subset_1(C_1024, k1_zfmisc_1(k2_zfmisc_1(A_1022, B_1023))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.02/3.46  tff(c_11020, plain, (![D_1025]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_1025)=k9_relat_1('#skF_9', D_1025))), inference(resolution, [status(thm)], [c_40, c_11013])).
% 10.02/3.46  tff(c_6473, plain, (![A_703, B_704, C_705, D_706]: (k7_relset_1(A_703, B_704, C_705, D_706)=k9_relat_1(C_705, D_706) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(A_703, B_704))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.02/3.46  tff(c_6480, plain, (![D_706]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_706)=k9_relat_1('#skF_9', D_706))), inference(resolution, [status(thm)], [c_40, c_6473])).
% 10.02/3.46  tff(c_1871, plain, (![A_371, B_372, C_373, D_374]: (k7_relset_1(A_371, B_372, C_373, D_374)=k9_relat_1(C_373, D_374) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.02/3.46  tff(c_1878, plain, (![D_374]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_374)=k9_relat_1('#skF_9', D_374))), inference(resolution, [status(thm)], [c_40, c_1871])).
% 10.02/3.46  tff(c_62, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_83, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_62])).
% 10.02/3.46  tff(c_54, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_72, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 10.02/3.46  tff(c_58, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_86, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_58])).
% 10.02/3.46  tff(c_580, plain, (![A_229, B_230, C_231, D_232]: (k7_relset_1(A_229, B_230, C_231, D_232)=k9_relat_1(C_231, D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.02/3.46  tff(c_587, plain, (![D_232]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_232)=k9_relat_1('#skF_9', D_232))), inference(resolution, [status(thm)], [c_40, c_580])).
% 10.02/3.46  tff(c_48, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_442, plain, (~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_48])).
% 10.02/3.46  tff(c_588, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_587, c_442])).
% 10.02/3.46  tff(c_16, plain, (![C_29, A_14, D_32]: (r2_hidden(C_29, k1_relat_1(A_14)) | ~r2_hidden(k4_tarski(C_29, D_32), A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.02/3.46  tff(c_96, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_86, c_16])).
% 10.02/3.46  tff(c_1373, plain, (![A_305, C_306, B_307, D_308]: (r2_hidden(A_305, k9_relat_1(C_306, B_307)) | ~r2_hidden(D_308, B_307) | ~r2_hidden(k4_tarski(D_308, A_305), C_306) | ~r2_hidden(D_308, k1_relat_1(C_306)) | ~v1_relat_1(C_306))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.02/3.46  tff(c_1484, plain, (![A_312, C_313]: (r2_hidden(A_312, k9_relat_1(C_313, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', A_312), C_313) | ~r2_hidden('#skF_11', k1_relat_1(C_313)) | ~v1_relat_1(C_313))), inference(resolution, [status(thm)], [c_72, c_1373])).
% 10.02/3.46  tff(c_1554, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_11', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_86, c_1484])).
% 10.02/3.46  tff(c_1576, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_96, c_1554])).
% 10.02/3.46  tff(c_1578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_1576])).
% 10.02/3.46  tff(c_1591, plain, (![F_314]: (~r2_hidden(F_314, '#skF_7') | ~r2_hidden(k4_tarski(F_314, '#skF_10'), '#skF_9') | ~m1_subset_1(F_314, '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 10.02/3.46  tff(c_1598, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_86, c_1591])).
% 10.02/3.46  tff(c_1605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_1598])).
% 10.02/3.46  tff(c_1606, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 10.02/3.46  tff(c_1883, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1878, c_1606])).
% 10.02/3.46  tff(c_34, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_5'(A_35, B_36, C_37), k1_relat_1(C_37)) | ~r2_hidden(A_35, k9_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.02/3.46  tff(c_1694, plain, (![C_336, A_337]: (r2_hidden(k4_tarski(C_336, '#skF_4'(A_337, k1_relat_1(A_337), C_336)), A_337) | ~r2_hidden(C_336, k1_relat_1(A_337)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.02/3.46  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.02/3.46  tff(c_5703, plain, (![C_619, A_620, A_621]: (r2_hidden(k4_tarski(C_619, '#skF_4'(A_620, k1_relat_1(A_620), C_619)), A_621) | ~m1_subset_1(A_620, k1_zfmisc_1(A_621)) | ~r2_hidden(C_619, k1_relat_1(A_620)))), inference(resolution, [status(thm)], [c_1694, c_8])).
% 10.02/3.46  tff(c_5840, plain, (![C_622, A_623, A_624]: (r2_hidden(C_622, k1_relat_1(A_623)) | ~m1_subset_1(A_624, k1_zfmisc_1(A_623)) | ~r2_hidden(C_622, k1_relat_1(A_624)))), inference(resolution, [status(thm)], [c_5703, c_16])).
% 10.02/3.46  tff(c_5864, plain, (![C_625]: (r2_hidden(C_625, k1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~r2_hidden(C_625, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_40, c_5840])).
% 10.02/3.46  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.02/3.46  tff(c_1717, plain, (![C_336, C_3, D_4]: (r2_hidden(C_336, C_3) | ~r2_hidden(C_336, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_1694, c_6])).
% 10.02/3.46  tff(c_5982, plain, (![C_626]: (r2_hidden(C_626, '#skF_8') | ~r2_hidden(C_626, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_5864, c_1717])).
% 10.02/3.46  tff(c_6026, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k9_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_5982])).
% 10.02/3.46  tff(c_6056, plain, (![A_628, B_629]: (r2_hidden('#skF_5'(A_628, B_629, '#skF_9'), '#skF_8') | ~r2_hidden(A_628, k9_relat_1('#skF_9', B_629)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_6026])).
% 10.02/3.46  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.02/3.46  tff(c_6082, plain, (![A_630, B_631]: (m1_subset_1('#skF_5'(A_630, B_631, '#skF_9'), '#skF_8') | ~r2_hidden(A_630, k9_relat_1('#skF_9', B_631)))), inference(resolution, [status(thm)], [c_6056, c_10])).
% 10.02/3.46  tff(c_6145, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1883, c_6082])).
% 10.02/3.46  tff(c_30, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_5'(A_35, B_36, C_37), B_36) | ~r2_hidden(A_35, k9_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.02/3.46  tff(c_1979, plain, (![A_391, B_392, C_393]: (r2_hidden(k4_tarski('#skF_5'(A_391, B_392, C_393), A_391), C_393) | ~r2_hidden(A_391, k9_relat_1(C_393, B_392)) | ~v1_relat_1(C_393))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.02/3.46  tff(c_1607, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_58])).
% 10.02/3.46  tff(c_56, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_1869, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1607, c_56])).
% 10.02/3.46  tff(c_1986, plain, (![B_392]: (~r2_hidden('#skF_5'('#skF_10', B_392, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_392, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_392)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1979, c_1869])).
% 10.02/3.46  tff(c_6190, plain, (![B_638]: (~r2_hidden('#skF_5'('#skF_10', B_638, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_638, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_638)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1986])).
% 10.02/3.46  tff(c_6198, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_6190])).
% 10.02/3.46  tff(c_6205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_1883, c_6145, c_6198])).
% 10.02/3.46  tff(c_6206, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 10.02/3.46  tff(c_6485, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6480, c_6206])).
% 10.02/3.46  tff(c_6298, plain, (![C_669, A_670]: (r2_hidden(k4_tarski(C_669, '#skF_4'(A_670, k1_relat_1(A_670), C_669)), A_670) | ~r2_hidden(C_669, k1_relat_1(A_670)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.02/3.46  tff(c_9999, plain, (![C_938, A_939, A_940]: (r2_hidden(k4_tarski(C_938, '#skF_4'(A_939, k1_relat_1(A_939), C_938)), A_940) | ~m1_subset_1(A_939, k1_zfmisc_1(A_940)) | ~r2_hidden(C_938, k1_relat_1(A_939)))), inference(resolution, [status(thm)], [c_6298, c_8])).
% 10.02/3.46  tff(c_10129, plain, (![C_941, A_942, A_943]: (r2_hidden(C_941, k1_relat_1(A_942)) | ~m1_subset_1(A_943, k1_zfmisc_1(A_942)) | ~r2_hidden(C_941, k1_relat_1(A_943)))), inference(resolution, [status(thm)], [c_9999, c_16])).
% 10.02/3.46  tff(c_10149, plain, (![C_944]: (r2_hidden(C_944, k1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~r2_hidden(C_944, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_40, c_10129])).
% 10.02/3.46  tff(c_6322, plain, (![C_669, C_3, D_4]: (r2_hidden(C_669, C_3) | ~r2_hidden(C_669, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_6298, c_6])).
% 10.02/3.46  tff(c_10260, plain, (![C_945]: (r2_hidden(C_945, '#skF_8') | ~r2_hidden(C_945, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_10149, c_6322])).
% 10.02/3.46  tff(c_10304, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k9_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_10260])).
% 10.02/3.46  tff(c_10334, plain, (![A_947, B_948]: (r2_hidden('#skF_5'(A_947, B_948, '#skF_9'), '#skF_8') | ~r2_hidden(A_947, k9_relat_1('#skF_9', B_948)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_10304])).
% 10.02/3.46  tff(c_10360, plain, (![A_949, B_950]: (m1_subset_1('#skF_5'(A_949, B_950, '#skF_9'), '#skF_8') | ~r2_hidden(A_949, k9_relat_1('#skF_9', B_950)))), inference(resolution, [status(thm)], [c_10334, c_10])).
% 10.02/3.46  tff(c_10423, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_6485, c_10360])).
% 10.02/3.46  tff(c_6545, plain, (![A_711, B_712, C_713]: (r2_hidden(k4_tarski('#skF_5'(A_711, B_712, C_713), A_711), C_713) | ~r2_hidden(A_711, k9_relat_1(C_713, B_712)) | ~v1_relat_1(C_713))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.02/3.46  tff(c_6207, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_62])).
% 10.02/3.46  tff(c_60, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_6285, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_6207, c_60])).
% 10.02/3.46  tff(c_6559, plain, (![B_712]: (~r2_hidden('#skF_5'('#skF_10', B_712, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_712, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_712)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_6545, c_6285])).
% 10.02/3.46  tff(c_10805, plain, (![B_965]: (~r2_hidden('#skF_5'('#skF_10', B_965, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_965, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_965)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_6559])).
% 10.02/3.46  tff(c_10813, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_10805])).
% 10.02/3.46  tff(c_10820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_6485, c_10423, c_10813])).
% 10.02/3.46  tff(c_10821, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 10.02/3.46  tff(c_11025, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11020, c_10821])).
% 10.02/3.46  tff(c_11035, plain, (![A_1027, B_1028, C_1029]: (r2_hidden(k4_tarski('#skF_5'(A_1027, B_1028, C_1029), A_1027), C_1029) | ~r2_hidden(A_1027, k9_relat_1(C_1029, B_1028)) | ~v1_relat_1(C_1029))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.02/3.46  tff(c_10822, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 10.02/3.46  tff(c_52, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.02/3.46  tff(c_10875, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_10822, c_52])).
% 10.02/3.46  tff(c_11049, plain, (![B_1028]: (~r2_hidden('#skF_5'('#skF_10', B_1028, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1028, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_1028)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_11035, c_10875])).
% 10.02/3.46  tff(c_11448, plain, (![B_1068]: (~r2_hidden('#skF_5'('#skF_10', B_1068, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1068, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_1068)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_11049])).
% 10.02/3.46  tff(c_11452, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_11448])).
% 10.02/3.46  tff(c_11455, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_11025, c_11452])).
% 10.02/3.46  tff(c_10877, plain, (![C_993, A_994]: (r2_hidden(k4_tarski(C_993, '#skF_4'(A_994, k1_relat_1(A_994), C_993)), A_994) | ~r2_hidden(C_993, k1_relat_1(A_994)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.02/3.46  tff(c_13867, plain, (![C_1237, A_1238, A_1239]: (r2_hidden(k4_tarski(C_1237, '#skF_4'(A_1238, k1_relat_1(A_1238), C_1237)), A_1239) | ~m1_subset_1(A_1238, k1_zfmisc_1(A_1239)) | ~r2_hidden(C_1237, k1_relat_1(A_1238)))), inference(resolution, [status(thm)], [c_10877, c_8])).
% 10.02/3.46  tff(c_13990, plain, (![C_1240, A_1241, A_1242]: (r2_hidden(C_1240, k1_relat_1(A_1241)) | ~m1_subset_1(A_1242, k1_zfmisc_1(A_1241)) | ~r2_hidden(C_1240, k1_relat_1(A_1242)))), inference(resolution, [status(thm)], [c_13867, c_16])).
% 10.02/3.46  tff(c_14014, plain, (![C_1243]: (r2_hidden(C_1243, k1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~r2_hidden(C_1243, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_40, c_13990])).
% 10.02/3.46  tff(c_10898, plain, (![C_993, C_3, D_4]: (r2_hidden(C_993, C_3) | ~r2_hidden(C_993, k1_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_10877, c_6])).
% 10.02/3.46  tff(c_14109, plain, (![C_1244]: (r2_hidden(C_1244, '#skF_8') | ~r2_hidden(C_1244, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_14014, c_10898])).
% 10.02/3.46  tff(c_14153, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k9_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_14109])).
% 10.02/3.46  tff(c_14183, plain, (![A_1246, B_1247]: (r2_hidden('#skF_5'(A_1246, B_1247, '#skF_9'), '#skF_8') | ~r2_hidden(A_1246, k9_relat_1('#skF_9', B_1247)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_14153])).
% 10.02/3.46  tff(c_14215, plain, (![A_1248, B_1249]: (m1_subset_1('#skF_5'(A_1248, B_1249, '#skF_9'), '#skF_8') | ~r2_hidden(A_1248, k9_relat_1('#skF_9', B_1249)))), inference(resolution, [status(thm)], [c_14183, c_10])).
% 10.02/3.46  tff(c_14250, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_11025, c_14215])).
% 10.02/3.46  tff(c_14280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11455, c_14250])).
% 10.02/3.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.02/3.46  
% 10.02/3.46  Inference rules
% 10.02/3.46  ----------------------
% 10.02/3.46  #Ref     : 0
% 10.02/3.46  #Sup     : 3642
% 10.02/3.46  #Fact    : 0
% 10.02/3.46  #Define  : 0
% 10.02/3.46  #Split   : 8
% 10.02/3.46  #Chain   : 0
% 10.02/3.46  #Close   : 0
% 10.02/3.46  
% 10.02/3.46  Ordering : KBO
% 10.02/3.46  
% 10.02/3.46  Simplification rules
% 10.02/3.46  ----------------------
% 10.02/3.46  #Subsume      : 131
% 10.02/3.46  #Demod        : 126
% 10.02/3.46  #Tautology    : 86
% 10.02/3.46  #SimpNegUnit  : 5
% 10.02/3.46  #BackRed      : 25
% 10.02/3.46  
% 10.02/3.46  #Partial instantiations: 0
% 10.02/3.46  #Strategies tried      : 1
% 10.02/3.46  
% 10.02/3.46  Timing (in seconds)
% 10.02/3.46  ----------------------
% 10.02/3.47  Preprocessing        : 0.34
% 10.02/3.47  Parsing              : 0.17
% 10.02/3.47  CNF conversion       : 0.03
% 10.02/3.47  Main loop            : 2.34
% 10.02/3.47  Inferencing          : 0.66
% 10.02/3.47  Reduction            : 0.58
% 10.02/3.47  Demodulation         : 0.38
% 10.02/3.47  BG Simplification    : 0.10
% 10.02/3.47  Subsumption          : 0.78
% 10.02/3.47  Abstraction          : 0.12
% 10.02/3.47  MUC search           : 0.00
% 10.02/3.47  Cooper               : 0.00
% 10.02/3.47  Total                : 2.73
% 10.02/3.47  Index Insertion      : 0.00
% 10.02/3.47  Index Deletion       : 0.00
% 10.02/3.47  Index Matching       : 0.00
% 10.02/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
