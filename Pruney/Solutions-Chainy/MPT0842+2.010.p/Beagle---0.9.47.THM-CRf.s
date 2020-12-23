%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:36 EST 2020

% Result     : Theorem 9.98s
% Output     : CNFRefutation 9.98s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 287 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  235 ( 834 expanded)
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

tff(f_96,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

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

tff(c_38,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    ! [C_134,A_135,B_136] :
      ( v1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_10670,plain,(
    ! [A_969,B_970,C_971,D_972] :
      ( k8_relset_1(A_969,B_970,C_971,D_972) = k10_relat_1(C_971,D_972)
      | ~ m1_subset_1(C_971,k1_zfmisc_1(k2_zfmisc_1(A_969,B_970))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10677,plain,(
    ! [D_972] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_972) = k10_relat_1('#skF_9',D_972) ),
    inference(resolution,[status(thm)],[c_38,c_10670])).

tff(c_6156,plain,(
    ! [A_665,B_666,C_667,D_668] :
      ( k8_relset_1(A_665,B_666,C_667,D_668) = k10_relat_1(C_667,D_668)
      | ~ m1_subset_1(C_667,k1_zfmisc_1(k2_zfmisc_1(A_665,B_666))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6163,plain,(
    ! [D_668] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_668) = k10_relat_1('#skF_9',D_668) ),
    inference(resolution,[status(thm)],[c_38,c_6156])).

tff(c_1719,plain,(
    ! [A_358,B_359,C_360,D_361] :
      ( k8_relset_1(A_358,B_359,C_360,D_361) = k10_relat_1(C_360,D_361)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_358,B_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1726,plain,(
    ! [D_361] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_361) = k10_relat_1('#skF_9',D_361) ),
    inference(resolution,[status(thm)],[c_38,c_1719])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_68,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_81,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_374,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k8_relset_1(A_199,B_200,C_201,D_202) = k10_relat_1(C_201,D_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_381,plain,(
    ! [D_202] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_202) = k10_relat_1('#skF_9',D_202) ),
    inference(resolution,[status(thm)],[c_38,c_374])).

tff(c_46,plain,(
    ! [F_131] :
      ( ~ r2_hidden(F_131,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_131),'#skF_9')
      | ~ m1_subset_1(F_131,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_331,plain,(
    ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_382,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_331])).

tff(c_14,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k2_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(D_29,C_26),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_81,c_14])).

tff(c_1171,plain,(
    ! [A_283,C_284,B_285,D_286] :
      ( r2_hidden(A_283,k10_relat_1(C_284,B_285))
      | ~ r2_hidden(D_286,B_285)
      | ~ r2_hidden(k4_tarski(A_283,D_286),C_284)
      | ~ r2_hidden(D_286,k2_relat_1(C_284))
      | ~ v1_relat_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1324,plain,(
    ! [A_293,C_294] :
      ( r2_hidden(A_293,k10_relat_1(C_294,'#skF_7'))
      | ~ r2_hidden(k4_tarski(A_293,'#skF_11'),C_294)
      | ~ r2_hidden('#skF_11',k2_relat_1(C_294))
      | ~ v1_relat_1(C_294) ) ),
    inference(resolution,[status(thm)],[c_68,c_1171])).

tff(c_1386,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_81,c_1324])).

tff(c_1404,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_92,c_1386])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_1404])).

tff(c_1441,plain,(
    ! [F_301] :
      ( ~ r2_hidden(F_301,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_301),'#skF_9')
      | ~ m1_subset_1(F_301,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1448,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_81,c_1441])).

tff(c_1455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_68,c_1448])).

tff(c_1456,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1731,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1456])).

tff(c_30,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_5'(A_30,B_31,C_32),k2_relat_1(C_32))
      | ~ r2_hidden(A_30,k10_relat_1(C_32,B_31))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1475,plain,(
    ! [A_306,C_307] :
      ( r2_hidden(k4_tarski('#skF_4'(A_306,k2_relat_1(A_306),C_307),C_307),A_306)
      | ~ r2_hidden(C_307,k2_relat_1(A_306)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5429,plain,(
    ! [A_590,C_591,A_592] :
      ( r2_hidden(k4_tarski('#skF_4'(A_590,k2_relat_1(A_590),C_591),C_591),A_592)
      | ~ m1_subset_1(A_590,k1_zfmisc_1(A_592))
      | ~ r2_hidden(C_591,k2_relat_1(A_590)) ) ),
    inference(resolution,[status(thm)],[c_1475,c_8])).

tff(c_5554,plain,(
    ! [C_593,A_594,A_595] :
      ( r2_hidden(C_593,k2_relat_1(A_594))
      | ~ m1_subset_1(A_595,k1_zfmisc_1(A_594))
      | ~ r2_hidden(C_593,k2_relat_1(A_595)) ) ),
    inference(resolution,[status(thm)],[c_5429,c_14])).

tff(c_5578,plain,(
    ! [C_596] :
      ( r2_hidden(C_596,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_596,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_38,c_5554])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1493,plain,(
    ! [C_307,D_4,C_3] :
      ( r2_hidden(C_307,D_4)
      | ~ r2_hidden(C_307,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_1475,c_4])).

tff(c_5691,plain,(
    ! [C_597] :
      ( r2_hidden(C_597,'#skF_8')
      | ~ r2_hidden(C_597,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_5578,c_1493])).

tff(c_5731,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_5'(A_30,B_31,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_30,k10_relat_1('#skF_9',B_31))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_5691])).

tff(c_5760,plain,(
    ! [A_599,B_600] :
      ( r2_hidden('#skF_5'(A_599,B_600,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_599,k10_relat_1('#skF_9',B_600)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5731])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5789,plain,(
    ! [A_601,B_602] :
      ( m1_subset_1('#skF_5'(A_601,B_602,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_601,k10_relat_1('#skF_9',B_602)) ) ),
    inference(resolution,[status(thm)],[c_5760,c_10])).

tff(c_5847,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1731,c_5789])).

tff(c_26,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_5'(A_30,B_31,C_32),B_31)
      | ~ r2_hidden(A_30,k10_relat_1(C_32,B_31))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1806,plain,(
    ! [A_371,B_372,C_373] :
      ( r2_hidden(k4_tarski(A_371,'#skF_5'(A_371,B_372,C_373)),C_373)
      | ~ r2_hidden(A_371,k10_relat_1(C_373,B_372))
      | ~ v1_relat_1(C_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1457,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_131] :
      ( ~ r2_hidden(F_131,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_131),'#skF_9')
      | ~ m1_subset_1(F_131,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1683,plain,(
    ! [F_131] :
      ( ~ r2_hidden(F_131,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_131),'#skF_9')
      | ~ m1_subset_1(F_131,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1457,c_54])).

tff(c_1810,plain,(
    ! [B_372] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_372,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_372,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_372))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1806,c_1683])).

tff(c_5876,plain,(
    ! [B_607] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_607,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_607,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_607)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1810])).

tff(c_5884,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_5876])).

tff(c_5891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1731,c_5847,c_5884])).

tff(c_5892,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6168,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6163,c_5892])).

tff(c_5904,plain,(
    ! [A_610,C_611] :
      ( r2_hidden(k4_tarski('#skF_4'(A_610,k2_relat_1(A_610),C_611),C_611),A_610)
      | ~ r2_hidden(C_611,k2_relat_1(A_610)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9062,plain,(
    ! [A_867,C_868,A_869] :
      ( r2_hidden(k4_tarski('#skF_4'(A_867,k2_relat_1(A_867),C_868),C_868),A_869)
      | ~ m1_subset_1(A_867,k1_zfmisc_1(A_869))
      | ~ r2_hidden(C_868,k2_relat_1(A_867)) ) ),
    inference(resolution,[status(thm)],[c_5904,c_8])).

tff(c_9181,plain,(
    ! [C_870,A_871,A_872] :
      ( r2_hidden(C_870,k2_relat_1(A_871))
      | ~ m1_subset_1(A_872,k1_zfmisc_1(A_871))
      | ~ r2_hidden(C_870,k2_relat_1(A_872)) ) ),
    inference(resolution,[status(thm)],[c_9062,c_14])).

tff(c_9205,plain,(
    ! [C_873] :
      ( r2_hidden(C_873,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_873,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_38,c_9181])).

tff(c_5922,plain,(
    ! [C_611,D_4,C_3] :
      ( r2_hidden(C_611,D_4)
      | ~ r2_hidden(C_611,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_5904,c_4])).

tff(c_9307,plain,(
    ! [C_874] :
      ( r2_hidden(C_874,'#skF_8')
      | ~ r2_hidden(C_874,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_9205,c_5922])).

tff(c_9343,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_5'(A_30,B_31,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_30,k10_relat_1('#skF_9',B_31))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_9307])).

tff(c_9371,plain,(
    ! [A_876,B_877] :
      ( r2_hidden('#skF_5'(A_876,B_877,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_876,k10_relat_1('#skF_9',B_877)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9343])).

tff(c_9397,plain,(
    ! [A_878,B_879] :
      ( m1_subset_1('#skF_5'(A_878,B_879,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_878,k10_relat_1('#skF_9',B_879)) ) ),
    inference(resolution,[status(thm)],[c_9371,c_10])).

tff(c_9450,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6168,c_9397])).

tff(c_6375,plain,(
    ! [A_697,B_698,C_699] :
      ( r2_hidden(k4_tarski(A_697,'#skF_5'(A_697,B_698,C_699)),C_699)
      | ~ r2_hidden(A_697,k10_relat_1(C_699,B_698))
      | ~ v1_relat_1(C_699) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5893,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_131] :
      ( ~ r2_hidden(F_131,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_131),'#skF_9')
      | ~ m1_subset_1(F_131,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6052,plain,(
    ! [F_131] :
      ( ~ r2_hidden(F_131,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_131),'#skF_9')
      | ~ m1_subset_1(F_131,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5893,c_58])).

tff(c_6390,plain,(
    ! [B_698] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_698,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_698,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_698))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_6375,c_6052])).

tff(c_10465,plain,(
    ! [B_915] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_915,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_915,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_915)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6390])).

tff(c_10473,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_10465])).

tff(c_10480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6168,c_9450,c_10473])).

tff(c_10481,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10682,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10677,c_10481])).

tff(c_10708,plain,(
    ! [A_974,B_975,C_976] :
      ( r2_hidden(k4_tarski(A_974,'#skF_5'(A_974,B_975,C_976)),C_976)
      | ~ r2_hidden(A_974,k10_relat_1(C_976,B_975))
      | ~ v1_relat_1(C_976) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10482,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [F_131] :
      ( ~ r2_hidden(F_131,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_131),'#skF_9')
      | ~ m1_subset_1(F_131,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10557,plain,(
    ! [F_131] :
      ( ~ r2_hidden(F_131,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_131),'#skF_9')
      | ~ m1_subset_1(F_131,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10482,c_50])).

tff(c_10720,plain,(
    ! [B_975] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_975,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_975,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_975))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_10708,c_10557])).

tff(c_11315,plain,(
    ! [B_1043] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1043,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1043,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1043)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10720])).

tff(c_11319,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_11315])).

tff(c_11322,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10682,c_11319])).

tff(c_10504,plain,(
    ! [A_931,C_932] :
      ( r2_hidden(k4_tarski('#skF_4'(A_931,k2_relat_1(A_931),C_932),C_932),A_931)
      | ~ r2_hidden(C_932,k2_relat_1(A_931)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12952,plain,(
    ! [A_1158,C_1159,A_1160] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1158,k2_relat_1(A_1158),C_1159),C_1159),A_1160)
      | ~ m1_subset_1(A_1158,k1_zfmisc_1(A_1160))
      | ~ r2_hidden(C_1159,k2_relat_1(A_1158)) ) ),
    inference(resolution,[status(thm)],[c_10504,c_8])).

tff(c_13063,plain,(
    ! [C_1161,A_1162,A_1163] :
      ( r2_hidden(C_1161,k2_relat_1(A_1162))
      | ~ m1_subset_1(A_1163,k1_zfmisc_1(A_1162))
      | ~ r2_hidden(C_1161,k2_relat_1(A_1163)) ) ),
    inference(resolution,[status(thm)],[c_12952,c_14])).

tff(c_13087,plain,(
    ! [C_1164] :
      ( r2_hidden(C_1164,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_1164,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_38,c_13063])).

tff(c_10521,plain,(
    ! [C_932,D_4,C_3] :
      ( r2_hidden(C_932,D_4)
      | ~ r2_hidden(C_932,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_10504,c_4])).

tff(c_13175,plain,(
    ! [C_1165] :
      ( r2_hidden(C_1165,'#skF_8')
      | ~ r2_hidden(C_1165,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_13087,c_10521])).

tff(c_13211,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_5'(A_30,B_31,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_30,k10_relat_1('#skF_9',B_31))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_13175])).

tff(c_13239,plain,(
    ! [A_1167,B_1168] :
      ( r2_hidden('#skF_5'(A_1167,B_1168,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1167,k10_relat_1('#skF_9',B_1168)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13211])).

tff(c_13271,plain,(
    ! [A_1169,B_1170] :
      ( m1_subset_1('#skF_5'(A_1169,B_1170,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1169,k10_relat_1('#skF_9',B_1170)) ) ),
    inference(resolution,[status(thm)],[c_13239,c_10])).

tff(c_13302,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_10682,c_13271])).

tff(c_13327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11322,c_13302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:33:56 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.98/3.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.45  
% 9.98/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.45  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 9.98/3.45  
% 9.98/3.45  %Foreground sorts:
% 9.98/3.45  
% 9.98/3.45  
% 9.98/3.45  %Background operators:
% 9.98/3.45  
% 9.98/3.45  
% 9.98/3.45  %Foreground operators:
% 9.98/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.98/3.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.98/3.45  tff('#skF_11', type, '#skF_11': $i).
% 9.98/3.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.98/3.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 9.98/3.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.98/3.45  tff('#skF_7', type, '#skF_7': $i).
% 9.98/3.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.98/3.45  tff('#skF_10', type, '#skF_10': $i).
% 9.98/3.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.98/3.45  tff('#skF_6', type, '#skF_6': $i).
% 9.98/3.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.98/3.45  tff('#skF_9', type, '#skF_9': $i).
% 9.98/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.98/3.45  tff('#skF_8', type, '#skF_8': $i).
% 9.98/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.98/3.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.98/3.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.98/3.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.98/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.98/3.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.98/3.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.98/3.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.98/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.98/3.45  
% 9.98/3.47  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 9.98/3.47  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.98/3.47  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 9.98/3.47  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 9.98/3.47  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 9.98/3.47  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.98/3.47  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 9.98/3.47  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.98/3.47  tff(c_38, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_62, plain, (![C_134, A_135, B_136]: (v1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.98/3.47  tff(c_66, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_62])).
% 9.98/3.47  tff(c_10670, plain, (![A_969, B_970, C_971, D_972]: (k8_relset_1(A_969, B_970, C_971, D_972)=k10_relat_1(C_971, D_972) | ~m1_subset_1(C_971, k1_zfmisc_1(k2_zfmisc_1(A_969, B_970))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.98/3.47  tff(c_10677, plain, (![D_972]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_972)=k10_relat_1('#skF_9', D_972))), inference(resolution, [status(thm)], [c_38, c_10670])).
% 9.98/3.47  tff(c_6156, plain, (![A_665, B_666, C_667, D_668]: (k8_relset_1(A_665, B_666, C_667, D_668)=k10_relat_1(C_667, D_668) | ~m1_subset_1(C_667, k1_zfmisc_1(k2_zfmisc_1(A_665, B_666))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.98/3.47  tff(c_6163, plain, (![D_668]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_668)=k10_relat_1('#skF_9', D_668))), inference(resolution, [status(thm)], [c_38, c_6156])).
% 9.98/3.47  tff(c_1719, plain, (![A_358, B_359, C_360, D_361]: (k8_relset_1(A_358, B_359, C_360, D_361)=k10_relat_1(C_360, D_361) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_358, B_359))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.98/3.47  tff(c_1726, plain, (![D_361]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_361)=k10_relat_1('#skF_9', D_361))), inference(resolution, [status(thm)], [c_38, c_1719])).
% 9.98/3.47  tff(c_60, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_79, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_60])).
% 9.98/3.47  tff(c_52, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_68, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 9.98/3.47  tff(c_56, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_81, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_56])).
% 9.98/3.47  tff(c_374, plain, (![A_199, B_200, C_201, D_202]: (k8_relset_1(A_199, B_200, C_201, D_202)=k10_relat_1(C_201, D_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.98/3.47  tff(c_381, plain, (![D_202]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_202)=k10_relat_1('#skF_9', D_202))), inference(resolution, [status(thm)], [c_38, c_374])).
% 9.98/3.47  tff(c_46, plain, (![F_131]: (~r2_hidden(F_131, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_131), '#skF_9') | ~m1_subset_1(F_131, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_331, plain, (~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 9.98/3.47  tff(c_382, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_331])).
% 9.98/3.47  tff(c_14, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k2_relat_1(A_11)) | ~r2_hidden(k4_tarski(D_29, C_26), A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.98/3.47  tff(c_92, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_81, c_14])).
% 9.98/3.47  tff(c_1171, plain, (![A_283, C_284, B_285, D_286]: (r2_hidden(A_283, k10_relat_1(C_284, B_285)) | ~r2_hidden(D_286, B_285) | ~r2_hidden(k4_tarski(A_283, D_286), C_284) | ~r2_hidden(D_286, k2_relat_1(C_284)) | ~v1_relat_1(C_284))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.98/3.47  tff(c_1324, plain, (![A_293, C_294]: (r2_hidden(A_293, k10_relat_1(C_294, '#skF_7')) | ~r2_hidden(k4_tarski(A_293, '#skF_11'), C_294) | ~r2_hidden('#skF_11', k2_relat_1(C_294)) | ~v1_relat_1(C_294))), inference(resolution, [status(thm)], [c_68, c_1171])).
% 9.98/3.47  tff(c_1386, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_11', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_81, c_1324])).
% 9.98/3.47  tff(c_1404, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_92, c_1386])).
% 9.98/3.47  tff(c_1406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_1404])).
% 9.98/3.47  tff(c_1441, plain, (![F_301]: (~r2_hidden(F_301, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_301), '#skF_9') | ~m1_subset_1(F_301, '#skF_8'))), inference(splitRight, [status(thm)], [c_46])).
% 9.98/3.47  tff(c_1448, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_81, c_1441])).
% 9.98/3.47  tff(c_1455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_68, c_1448])).
% 9.98/3.47  tff(c_1456, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_56])).
% 9.98/3.47  tff(c_1731, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1456])).
% 9.98/3.47  tff(c_30, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_5'(A_30, B_31, C_32), k2_relat_1(C_32)) | ~r2_hidden(A_30, k10_relat_1(C_32, B_31)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.98/3.47  tff(c_1475, plain, (![A_306, C_307]: (r2_hidden(k4_tarski('#skF_4'(A_306, k2_relat_1(A_306), C_307), C_307), A_306) | ~r2_hidden(C_307, k2_relat_1(A_306)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.98/3.47  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.98/3.47  tff(c_5429, plain, (![A_590, C_591, A_592]: (r2_hidden(k4_tarski('#skF_4'(A_590, k2_relat_1(A_590), C_591), C_591), A_592) | ~m1_subset_1(A_590, k1_zfmisc_1(A_592)) | ~r2_hidden(C_591, k2_relat_1(A_590)))), inference(resolution, [status(thm)], [c_1475, c_8])).
% 9.98/3.47  tff(c_5554, plain, (![C_593, A_594, A_595]: (r2_hidden(C_593, k2_relat_1(A_594)) | ~m1_subset_1(A_595, k1_zfmisc_1(A_594)) | ~r2_hidden(C_593, k2_relat_1(A_595)))), inference(resolution, [status(thm)], [c_5429, c_14])).
% 9.98/3.47  tff(c_5578, plain, (![C_596]: (r2_hidden(C_596, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_596, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_38, c_5554])).
% 9.98/3.47  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.98/3.47  tff(c_1493, plain, (![C_307, D_4, C_3]: (r2_hidden(C_307, D_4) | ~r2_hidden(C_307, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_1475, c_4])).
% 9.98/3.47  tff(c_5691, plain, (![C_597]: (r2_hidden(C_597, '#skF_8') | ~r2_hidden(C_597, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_5578, c_1493])).
% 9.98/3.47  tff(c_5731, plain, (![A_30, B_31]: (r2_hidden('#skF_5'(A_30, B_31, '#skF_9'), '#skF_8') | ~r2_hidden(A_30, k10_relat_1('#skF_9', B_31)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_5691])).
% 9.98/3.47  tff(c_5760, plain, (![A_599, B_600]: (r2_hidden('#skF_5'(A_599, B_600, '#skF_9'), '#skF_8') | ~r2_hidden(A_599, k10_relat_1('#skF_9', B_600)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5731])).
% 9.98/3.47  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.98/3.47  tff(c_5789, plain, (![A_601, B_602]: (m1_subset_1('#skF_5'(A_601, B_602, '#skF_9'), '#skF_8') | ~r2_hidden(A_601, k10_relat_1('#skF_9', B_602)))), inference(resolution, [status(thm)], [c_5760, c_10])).
% 9.98/3.47  tff(c_5847, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1731, c_5789])).
% 9.98/3.47  tff(c_26, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_5'(A_30, B_31, C_32), B_31) | ~r2_hidden(A_30, k10_relat_1(C_32, B_31)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.98/3.47  tff(c_1806, plain, (![A_371, B_372, C_373]: (r2_hidden(k4_tarski(A_371, '#skF_5'(A_371, B_372, C_373)), C_373) | ~r2_hidden(A_371, k10_relat_1(C_373, B_372)) | ~v1_relat_1(C_373))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.98/3.47  tff(c_1457, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_56])).
% 9.98/3.47  tff(c_54, plain, (![F_131]: (~r2_hidden(F_131, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_131), '#skF_9') | ~m1_subset_1(F_131, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_1683, plain, (![F_131]: (~r2_hidden(F_131, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_131), '#skF_9') | ~m1_subset_1(F_131, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1457, c_54])).
% 9.98/3.47  tff(c_1810, plain, (![B_372]: (~r2_hidden('#skF_5'('#skF_10', B_372, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_372, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_372)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1806, c_1683])).
% 9.98/3.47  tff(c_5876, plain, (![B_607]: (~r2_hidden('#skF_5'('#skF_10', B_607, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_607, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_607)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1810])).
% 9.98/3.47  tff(c_5884, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_5876])).
% 9.98/3.47  tff(c_5891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1731, c_5847, c_5884])).
% 9.98/3.47  tff(c_5892, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 9.98/3.47  tff(c_6168, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6163, c_5892])).
% 9.98/3.47  tff(c_5904, plain, (![A_610, C_611]: (r2_hidden(k4_tarski('#skF_4'(A_610, k2_relat_1(A_610), C_611), C_611), A_610) | ~r2_hidden(C_611, k2_relat_1(A_610)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.98/3.47  tff(c_9062, plain, (![A_867, C_868, A_869]: (r2_hidden(k4_tarski('#skF_4'(A_867, k2_relat_1(A_867), C_868), C_868), A_869) | ~m1_subset_1(A_867, k1_zfmisc_1(A_869)) | ~r2_hidden(C_868, k2_relat_1(A_867)))), inference(resolution, [status(thm)], [c_5904, c_8])).
% 9.98/3.47  tff(c_9181, plain, (![C_870, A_871, A_872]: (r2_hidden(C_870, k2_relat_1(A_871)) | ~m1_subset_1(A_872, k1_zfmisc_1(A_871)) | ~r2_hidden(C_870, k2_relat_1(A_872)))), inference(resolution, [status(thm)], [c_9062, c_14])).
% 9.98/3.47  tff(c_9205, plain, (![C_873]: (r2_hidden(C_873, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_873, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_38, c_9181])).
% 9.98/3.47  tff(c_5922, plain, (![C_611, D_4, C_3]: (r2_hidden(C_611, D_4) | ~r2_hidden(C_611, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_5904, c_4])).
% 9.98/3.47  tff(c_9307, plain, (![C_874]: (r2_hidden(C_874, '#skF_8') | ~r2_hidden(C_874, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_9205, c_5922])).
% 9.98/3.47  tff(c_9343, plain, (![A_30, B_31]: (r2_hidden('#skF_5'(A_30, B_31, '#skF_9'), '#skF_8') | ~r2_hidden(A_30, k10_relat_1('#skF_9', B_31)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_9307])).
% 9.98/3.47  tff(c_9371, plain, (![A_876, B_877]: (r2_hidden('#skF_5'(A_876, B_877, '#skF_9'), '#skF_8') | ~r2_hidden(A_876, k10_relat_1('#skF_9', B_877)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9343])).
% 9.98/3.47  tff(c_9397, plain, (![A_878, B_879]: (m1_subset_1('#skF_5'(A_878, B_879, '#skF_9'), '#skF_8') | ~r2_hidden(A_878, k10_relat_1('#skF_9', B_879)))), inference(resolution, [status(thm)], [c_9371, c_10])).
% 9.98/3.47  tff(c_9450, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_6168, c_9397])).
% 9.98/3.47  tff(c_6375, plain, (![A_697, B_698, C_699]: (r2_hidden(k4_tarski(A_697, '#skF_5'(A_697, B_698, C_699)), C_699) | ~r2_hidden(A_697, k10_relat_1(C_699, B_698)) | ~v1_relat_1(C_699))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.98/3.47  tff(c_5893, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_60])).
% 9.98/3.47  tff(c_58, plain, (![F_131]: (~r2_hidden(F_131, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_131), '#skF_9') | ~m1_subset_1(F_131, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_6052, plain, (![F_131]: (~r2_hidden(F_131, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_131), '#skF_9') | ~m1_subset_1(F_131, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_5893, c_58])).
% 9.98/3.47  tff(c_6390, plain, (![B_698]: (~r2_hidden('#skF_5'('#skF_10', B_698, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_698, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_698)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_6375, c_6052])).
% 9.98/3.47  tff(c_10465, plain, (![B_915]: (~r2_hidden('#skF_5'('#skF_10', B_915, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_915, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_915)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6390])).
% 9.98/3.47  tff(c_10473, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_10465])).
% 9.98/3.47  tff(c_10480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_6168, c_9450, c_10473])).
% 9.98/3.47  tff(c_10481, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 9.98/3.47  tff(c_10682, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10677, c_10481])).
% 9.98/3.47  tff(c_10708, plain, (![A_974, B_975, C_976]: (r2_hidden(k4_tarski(A_974, '#skF_5'(A_974, B_975, C_976)), C_976) | ~r2_hidden(A_974, k10_relat_1(C_976, B_975)) | ~v1_relat_1(C_976))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.98/3.47  tff(c_10482, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 9.98/3.47  tff(c_50, plain, (![F_131]: (~r2_hidden(F_131, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_131), '#skF_9') | ~m1_subset_1(F_131, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.98/3.47  tff(c_10557, plain, (![F_131]: (~r2_hidden(F_131, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_131), '#skF_9') | ~m1_subset_1(F_131, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_10482, c_50])).
% 9.98/3.47  tff(c_10720, plain, (![B_975]: (~r2_hidden('#skF_5'('#skF_10', B_975, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_975, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_975)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_10708, c_10557])).
% 9.98/3.47  tff(c_11315, plain, (![B_1043]: (~r2_hidden('#skF_5'('#skF_10', B_1043, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1043, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1043)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10720])).
% 9.98/3.47  tff(c_11319, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_11315])).
% 9.98/3.47  tff(c_11322, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10682, c_11319])).
% 9.98/3.47  tff(c_10504, plain, (![A_931, C_932]: (r2_hidden(k4_tarski('#skF_4'(A_931, k2_relat_1(A_931), C_932), C_932), A_931) | ~r2_hidden(C_932, k2_relat_1(A_931)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.98/3.47  tff(c_12952, plain, (![A_1158, C_1159, A_1160]: (r2_hidden(k4_tarski('#skF_4'(A_1158, k2_relat_1(A_1158), C_1159), C_1159), A_1160) | ~m1_subset_1(A_1158, k1_zfmisc_1(A_1160)) | ~r2_hidden(C_1159, k2_relat_1(A_1158)))), inference(resolution, [status(thm)], [c_10504, c_8])).
% 9.98/3.47  tff(c_13063, plain, (![C_1161, A_1162, A_1163]: (r2_hidden(C_1161, k2_relat_1(A_1162)) | ~m1_subset_1(A_1163, k1_zfmisc_1(A_1162)) | ~r2_hidden(C_1161, k2_relat_1(A_1163)))), inference(resolution, [status(thm)], [c_12952, c_14])).
% 9.98/3.47  tff(c_13087, plain, (![C_1164]: (r2_hidden(C_1164, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_1164, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_38, c_13063])).
% 9.98/3.47  tff(c_10521, plain, (![C_932, D_4, C_3]: (r2_hidden(C_932, D_4) | ~r2_hidden(C_932, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_10504, c_4])).
% 9.98/3.47  tff(c_13175, plain, (![C_1165]: (r2_hidden(C_1165, '#skF_8') | ~r2_hidden(C_1165, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_13087, c_10521])).
% 9.98/3.47  tff(c_13211, plain, (![A_30, B_31]: (r2_hidden('#skF_5'(A_30, B_31, '#skF_9'), '#skF_8') | ~r2_hidden(A_30, k10_relat_1('#skF_9', B_31)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_13175])).
% 9.98/3.47  tff(c_13239, plain, (![A_1167, B_1168]: (r2_hidden('#skF_5'(A_1167, B_1168, '#skF_9'), '#skF_8') | ~r2_hidden(A_1167, k10_relat_1('#skF_9', B_1168)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13211])).
% 9.98/3.47  tff(c_13271, plain, (![A_1169, B_1170]: (m1_subset_1('#skF_5'(A_1169, B_1170, '#skF_9'), '#skF_8') | ~r2_hidden(A_1169, k10_relat_1('#skF_9', B_1170)))), inference(resolution, [status(thm)], [c_13239, c_10])).
% 9.98/3.47  tff(c_13302, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_10682, c_13271])).
% 9.98/3.47  tff(c_13327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11322, c_13302])).
% 9.98/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.98/3.47  
% 9.98/3.47  Inference rules
% 9.98/3.47  ----------------------
% 9.98/3.47  #Ref     : 0
% 9.98/3.47  #Sup     : 3425
% 9.98/3.47  #Fact    : 0
% 9.98/3.47  #Define  : 0
% 9.98/3.47  #Split   : 8
% 9.98/3.47  #Chain   : 0
% 9.98/3.47  #Close   : 0
% 9.98/3.47  
% 9.98/3.47  Ordering : KBO
% 9.98/3.47  
% 9.98/3.47  Simplification rules
% 9.98/3.47  ----------------------
% 9.98/3.47  #Subsume      : 122
% 9.98/3.47  #Demod        : 102
% 9.98/3.47  #Tautology    : 87
% 9.98/3.47  #SimpNegUnit  : 6
% 9.98/3.47  #BackRed      : 24
% 9.98/3.47  
% 9.98/3.47  #Partial instantiations: 0
% 9.98/3.47  #Strategies tried      : 1
% 9.98/3.47  
% 9.98/3.47  Timing (in seconds)
% 9.98/3.47  ----------------------
% 9.98/3.47  Preprocessing        : 0.33
% 9.98/3.47  Parsing              : 0.16
% 9.98/3.47  CNF conversion       : 0.03
% 9.98/3.47  Main loop            : 2.37
% 9.98/3.47  Inferencing          : 0.67
% 9.98/3.47  Reduction            : 0.57
% 9.98/3.48  Demodulation         : 0.37
% 9.98/3.48  BG Simplification    : 0.10
% 9.98/3.48  Subsumption          : 0.80
% 9.98/3.48  Abstraction          : 0.12
% 9.98/3.48  MUC search           : 0.00
% 9.98/3.48  Cooper               : 0.00
% 9.98/3.48  Total                : 2.74
% 9.98/3.48  Index Insertion      : 0.00
% 9.98/3.48  Index Deletion       : 0.00
% 9.98/3.48  Index Matching       : 0.00
% 9.98/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
