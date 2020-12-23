%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:38 EST 2020

% Result     : Theorem 15.85s
% Output     : CNFRefutation 15.95s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 326 expanded)
%              Number of leaves         :   33 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 ( 948 expanded)
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
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k8_relset_1(A,C,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(E,F),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_51,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_32,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46669,plain,(
    ! [B_1821,A_1822] :
      ( v1_relat_1(B_1821)
      | ~ m1_subset_1(B_1821,k1_zfmisc_1(A_1822))
      | ~ v1_relat_1(A_1822) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46676,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_46,c_46669])).

tff(c_46680,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46676])).

tff(c_46832,plain,(
    ! [A_1864,B_1865,C_1866,D_1867] :
      ( k8_relset_1(A_1864,B_1865,C_1866,D_1867) = k10_relat_1(C_1866,D_1867)
      | ~ m1_subset_1(C_1866,k1_zfmisc_1(k2_zfmisc_1(A_1864,B_1865))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46839,plain,(
    ! [D_1867] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_1867) = k10_relat_1('#skF_9',D_1867) ),
    inference(resolution,[status(thm)],[c_46,c_46832])).

tff(c_96,plain,(
    ! [B_144,A_145] :
      ( v1_relat_1(B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_145))
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_46,c_96])).

tff(c_107,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_103])).

tff(c_37439,plain,(
    ! [A_1448,B_1449,C_1450,D_1451] :
      ( k8_relset_1(A_1448,B_1449,C_1450,D_1451) = k10_relat_1(C_1450,D_1451)
      | ~ m1_subset_1(C_1450,k1_zfmisc_1(k2_zfmisc_1(A_1448,B_1449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37446,plain,(
    ! [D_1451] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_1451) = k10_relat_1('#skF_9',D_1451) ),
    inference(resolution,[status(thm)],[c_46,c_37439])).

tff(c_21692,plain,(
    ! [A_961,B_962,C_963,D_964] :
      ( k8_relset_1(A_961,B_962,C_963,D_964) = k10_relat_1(C_963,D_964)
      | ~ m1_subset_1(C_963,k1_zfmisc_1(k2_zfmisc_1(A_961,B_962))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_21699,plain,(
    ! [D_964] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_964) = k10_relat_1('#skF_9',D_964) ),
    inference(resolution,[status(thm)],[c_46,c_21692])).

tff(c_68,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_85,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_116,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_154,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_614,plain,(
    ! [A_224,B_225,C_226,D_227] :
      ( k8_relset_1(A_224,B_225,C_226,D_227) = k10_relat_1(C_226,D_227)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_625,plain,(
    ! [D_227] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_227) = k10_relat_1('#skF_9',D_227) ),
    inference(resolution,[status(thm)],[c_46,c_614])).

tff(c_54,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_381,plain,(
    ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_628,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_381])).

tff(c_22,plain,(
    ! [C_29,A_14,D_32] :
      ( r2_hidden(C_29,k2_relat_1(A_14))
      | ~ r2_hidden(k4_tarski(D_32,C_29),A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_164,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_154,c_22])).

tff(c_1476,plain,(
    ! [A_289,C_290,B_291,D_292] :
      ( r2_hidden(A_289,k10_relat_1(C_290,B_291))
      | ~ r2_hidden(D_292,B_291)
      | ~ r2_hidden(k4_tarski(A_289,D_292),C_290)
      | ~ r2_hidden(D_292,k2_relat_1(C_290))
      | ~ v1_relat_1(C_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1729,plain,(
    ! [A_298,C_299] :
      ( r2_hidden(A_298,k10_relat_1(C_299,'#skF_7'))
      | ~ r2_hidden(k4_tarski(A_298,'#skF_11'),C_299)
      | ~ r2_hidden('#skF_11',k2_relat_1(C_299))
      | ~ v1_relat_1(C_299) ) ),
    inference(resolution,[status(thm)],[c_116,c_1476])).

tff(c_1803,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_154,c_1729])).

tff(c_1830,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_164,c_1803])).

tff(c_1832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_628,c_1830])).

tff(c_1842,plain,(
    ! [F_300] :
      ( ~ r2_hidden(F_300,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_300),'#skF_9')
      | ~ m1_subset_1(F_300,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1849,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_154,c_1842])).

tff(c_1859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_116,c_1849])).

tff(c_1860,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_21704,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21699,c_1860])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_5'(A_35,B_36,C_37),k2_relat_1(C_37))
      | ~ r2_hidden(A_35,k10_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_21488,plain,(
    ! [A_933,C_934] :
      ( r2_hidden(k4_tarski('#skF_4'(A_933,k2_relat_1(A_933),C_934),C_934),A_933)
      | ~ r2_hidden(C_934,k2_relat_1(A_933)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_35128,plain,(
    ! [A_1352,C_1353,A_1354] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1352,k2_relat_1(A_1352),C_1353),C_1353),A_1354)
      | ~ m1_subset_1(A_1352,k1_zfmisc_1(A_1354))
      | ~ r2_hidden(C_1353,k2_relat_1(A_1352)) ) ),
    inference(resolution,[status(thm)],[c_21488,c_16])).

tff(c_35340,plain,(
    ! [C_1355,A_1356,A_1357] :
      ( r2_hidden(C_1355,k2_relat_1(A_1356))
      | ~ m1_subset_1(A_1357,k1_zfmisc_1(A_1356))
      | ~ r2_hidden(C_1355,k2_relat_1(A_1357)) ) ),
    inference(resolution,[status(thm)],[c_35128,c_22])).

tff(c_35360,plain,(
    ! [C_1358] :
      ( r2_hidden(C_1358,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_1358,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_46,c_35340])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21506,plain,(
    ! [C_934,D_4,C_3] :
      ( r2_hidden(C_934,D_4)
      | ~ r2_hidden(C_934,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_21488,c_4])).

tff(c_35580,plain,(
    ! [C_1359] :
      ( r2_hidden(C_1359,'#skF_8')
      | ~ r2_hidden(C_1359,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_35360,c_21506])).

tff(c_35612,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k10_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_40,c_35580])).

tff(c_35668,plain,(
    ! [A_1362,B_1363] :
      ( r2_hidden('#skF_5'(A_1362,B_1363,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1362,k10_relat_1('#skF_9',B_1363)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_35612])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_35701,plain,(
    ! [A_1362,B_1363] :
      ( m1_subset_1('#skF_5'(A_1362,B_1363,'#skF_9'),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_1362,k10_relat_1('#skF_9',B_1363)) ) ),
    inference(resolution,[status(thm)],[c_35668,c_8])).

tff(c_35720,plain,(
    ! [A_1364,B_1365] :
      ( m1_subset_1('#skF_5'(A_1364,B_1365,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1364,k10_relat_1('#skF_9',B_1365)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_35701])).

tff(c_35777,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_21704,c_35720])).

tff(c_36,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_5'(A_35,B_36,C_37),B_36)
      | ~ r2_hidden(A_35,k10_relat_1(C_37,B_36))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22147,plain,(
    ! [A_1022,B_1023,C_1024] :
      ( r2_hidden(k4_tarski(A_1022,'#skF_5'(A_1022,B_1023,C_1024)),C_1024)
      | ~ r2_hidden(A_1022,k10_relat_1(C_1024,B_1023))
      | ~ v1_relat_1(C_1024) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1861,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_21726,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1861,c_62])).

tff(c_22158,plain,(
    ! [B_1023] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1023,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1023,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1023))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_22147,c_21726])).

tff(c_37215,plain,(
    ! [B_1404] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1404,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1404,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1404)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_22158])).

tff(c_37223,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_37215])).

tff(c_37233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_21704,c_35777,c_37223])).

tff(c_37234,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_37451,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37446,c_37234])).

tff(c_37278,plain,(
    ! [A_1420,C_1421] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1420,k2_relat_1(A_1420),C_1421),C_1421),A_1420)
      | ~ r2_hidden(C_1421,k2_relat_1(A_1420)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_45357,plain,(
    ! [A_1775,C_1776,A_1777] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1775,k2_relat_1(A_1775),C_1776),C_1776),A_1777)
      | ~ m1_subset_1(A_1775,k1_zfmisc_1(A_1777))
      | ~ r2_hidden(C_1776,k2_relat_1(A_1775)) ) ),
    inference(resolution,[status(thm)],[c_37278,c_16])).

tff(c_45537,plain,(
    ! [C_1778,A_1779,A_1780] :
      ( r2_hidden(C_1778,k2_relat_1(A_1779))
      | ~ m1_subset_1(A_1780,k1_zfmisc_1(A_1779))
      | ~ r2_hidden(C_1778,k2_relat_1(A_1780)) ) ),
    inference(resolution,[status(thm)],[c_45357,c_22])).

tff(c_45553,plain,(
    ! [C_1781] :
      ( r2_hidden(C_1781,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_1781,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_46,c_45537])).

tff(c_37297,plain,(
    ! [C_1421,D_4,C_3] :
      ( r2_hidden(C_1421,D_4)
      | ~ r2_hidden(C_1421,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_37278,c_4])).

tff(c_45732,plain,(
    ! [C_1782] :
      ( r2_hidden(C_1782,'#skF_8')
      | ~ r2_hidden(C_1782,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_45553,c_37297])).

tff(c_45768,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k10_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_40,c_45732])).

tff(c_45825,plain,(
    ! [A_1785,B_1786] :
      ( r2_hidden('#skF_5'(A_1785,B_1786,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1785,k10_relat_1('#skF_9',B_1786)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_45768])).

tff(c_45858,plain,(
    ! [A_1785,B_1786] :
      ( m1_subset_1('#skF_5'(A_1785,B_1786,'#skF_9'),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_1785,k10_relat_1('#skF_9',B_1786)) ) ),
    inference(resolution,[status(thm)],[c_45825,c_8])).

tff(c_45877,plain,(
    ! [A_1787,B_1788] :
      ( m1_subset_1('#skF_5'(A_1787,B_1788,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1787,k10_relat_1('#skF_9',B_1788)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_45858])).

tff(c_45932,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_37451,c_45877])).

tff(c_37743,plain,(
    ! [A_1491,B_1492,C_1493] :
      ( r2_hidden(k4_tarski(A_1491,'#skF_5'(A_1491,B_1492,C_1493)),C_1493)
      | ~ r2_hidden(A_1491,k10_relat_1(C_1493,B_1492))
      | ~ v1_relat_1(C_1493) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_37235,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_37409,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_37235,c_58])).

tff(c_37751,plain,(
    ! [B_1492] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1492,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1492,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1492))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_37743,c_37409])).

tff(c_46633,plain,(
    ! [B_1816] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1816,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1816,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1816)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_37751])).

tff(c_46641,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_46633])).

tff(c_46651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_37451,c_45932,c_46641])).

tff(c_46652,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_46842,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46839,c_46652])).

tff(c_47229,plain,(
    ! [A_1924,B_1925,C_1926] :
      ( r2_hidden(k4_tarski(A_1924,'#skF_5'(A_1924,B_1925,C_1926)),C_1926)
      | ~ r2_hidden(A_1924,k10_relat_1(C_1926,B_1925))
      | ~ v1_relat_1(C_1926) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46653,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46735,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_133),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46653,c_66])).

tff(c_47251,plain,(
    ! [B_1925] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1925,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1925,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1925))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_47229,c_46735])).

tff(c_48853,plain,(
    ! [B_2019] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_2019,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_2019,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_2019)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46680,c_47251])).

tff(c_48857,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_48853])).

tff(c_48863,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46680,c_46842,c_48857])).

tff(c_46742,plain,(
    ! [A_1848,C_1849] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1848,k2_relat_1(A_1848),C_1849),C_1849),A_1848)
      | ~ r2_hidden(C_1849,k2_relat_1(A_1848)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_56124,plain,(
    ! [A_2236,C_2237,A_2238] :
      ( r2_hidden(k4_tarski('#skF_4'(A_2236,k2_relat_1(A_2236),C_2237),C_2237),A_2238)
      | ~ m1_subset_1(A_2236,k1_zfmisc_1(A_2238))
      | ~ r2_hidden(C_2237,k2_relat_1(A_2236)) ) ),
    inference(resolution,[status(thm)],[c_46742,c_16])).

tff(c_56325,plain,(
    ! [C_2239,A_2240,A_2241] :
      ( r2_hidden(C_2239,k2_relat_1(A_2240))
      | ~ m1_subset_1(A_2241,k1_zfmisc_1(A_2240))
      | ~ r2_hidden(C_2239,k2_relat_1(A_2241)) ) ),
    inference(resolution,[status(thm)],[c_56124,c_22])).

tff(c_56349,plain,(
    ! [C_2242] :
      ( r2_hidden(C_2242,k2_relat_1(k2_zfmisc_1('#skF_6','#skF_8')))
      | ~ r2_hidden(C_2242,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_46,c_56325])).

tff(c_46761,plain,(
    ! [C_1849,D_4,C_3] :
      ( r2_hidden(C_1849,D_4)
      | ~ r2_hidden(C_1849,k2_relat_1(k2_zfmisc_1(C_3,D_4))) ) ),
    inference(resolution,[status(thm)],[c_46742,c_4])).

tff(c_56538,plain,(
    ! [C_2243] :
      ( r2_hidden(C_2243,'#skF_8')
      | ~ r2_hidden(C_2243,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_56349,c_46761])).

tff(c_56578,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_5'(A_35,B_36,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_35,k10_relat_1('#skF_9',B_36))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_40,c_56538])).

tff(c_56636,plain,(
    ! [A_2246,B_2247] :
      ( r2_hidden('#skF_5'(A_2246,B_2247,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_2246,k10_relat_1('#skF_9',B_2247)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46680,c_56578])).

tff(c_56673,plain,(
    ! [A_2246,B_2247] :
      ( m1_subset_1('#skF_5'(A_2246,B_2247,'#skF_9'),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_2246,k10_relat_1('#skF_9',B_2247)) ) ),
    inference(resolution,[status(thm)],[c_56636,c_8])).

tff(c_56694,plain,(
    ! [A_2248,B_2249] :
      ( m1_subset_1('#skF_5'(A_2248,B_2249,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_2248,k10_relat_1('#skF_9',B_2249)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_56673])).

tff(c_56725,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_46842,c_56694])).

tff(c_56752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48863,c_56725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.85/8.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.85/8.36  
% 15.85/8.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.95/8.37  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 15.95/8.37  
% 15.95/8.37  %Foreground sorts:
% 15.95/8.37  
% 15.95/8.37  
% 15.95/8.37  %Background operators:
% 15.95/8.37  
% 15.95/8.37  
% 15.95/8.37  %Foreground operators:
% 15.95/8.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.95/8.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.95/8.37  tff('#skF_11', type, '#skF_11': $i).
% 15.95/8.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.95/8.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 15.95/8.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 15.95/8.37  tff('#skF_7', type, '#skF_7': $i).
% 15.95/8.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.95/8.37  tff('#skF_10', type, '#skF_10': $i).
% 15.95/8.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.95/8.37  tff('#skF_6', type, '#skF_6': $i).
% 15.95/8.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 15.95/8.37  tff('#skF_9', type, '#skF_9': $i).
% 15.95/8.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.95/8.37  tff('#skF_8', type, '#skF_8': $i).
% 15.95/8.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.95/8.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 15.95/8.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.95/8.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.95/8.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.95/8.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.95/8.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.95/8.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.95/8.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.95/8.37  
% 15.95/8.39  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.95/8.39  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 15.95/8.39  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.95/8.39  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 15.95/8.39  tff(f_66, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 15.95/8.39  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 15.95/8.39  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 15.95/8.39  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 15.95/8.39  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.95/8.39  tff(c_32, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.95/8.39  tff(c_46, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_46669, plain, (![B_1821, A_1822]: (v1_relat_1(B_1821) | ~m1_subset_1(B_1821, k1_zfmisc_1(A_1822)) | ~v1_relat_1(A_1822))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.95/8.39  tff(c_46676, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_46, c_46669])).
% 15.95/8.39  tff(c_46680, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46676])).
% 15.95/8.39  tff(c_46832, plain, (![A_1864, B_1865, C_1866, D_1867]: (k8_relset_1(A_1864, B_1865, C_1866, D_1867)=k10_relat_1(C_1866, D_1867) | ~m1_subset_1(C_1866, k1_zfmisc_1(k2_zfmisc_1(A_1864, B_1865))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 15.95/8.39  tff(c_46839, plain, (![D_1867]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_1867)=k10_relat_1('#skF_9', D_1867))), inference(resolution, [status(thm)], [c_46, c_46832])).
% 15.95/8.39  tff(c_96, plain, (![B_144, A_145]: (v1_relat_1(B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(A_145)) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.95/8.39  tff(c_103, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_46, c_96])).
% 15.95/8.39  tff(c_107, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_103])).
% 15.95/8.39  tff(c_37439, plain, (![A_1448, B_1449, C_1450, D_1451]: (k8_relset_1(A_1448, B_1449, C_1450, D_1451)=k10_relat_1(C_1450, D_1451) | ~m1_subset_1(C_1450, k1_zfmisc_1(k2_zfmisc_1(A_1448, B_1449))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 15.95/8.39  tff(c_37446, plain, (![D_1451]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_1451)=k10_relat_1('#skF_9', D_1451))), inference(resolution, [status(thm)], [c_46, c_37439])).
% 15.95/8.39  tff(c_21692, plain, (![A_961, B_962, C_963, D_964]: (k8_relset_1(A_961, B_962, C_963, D_964)=k10_relat_1(C_963, D_964) | ~m1_subset_1(C_963, k1_zfmisc_1(k2_zfmisc_1(A_961, B_962))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 15.95/8.39  tff(c_21699, plain, (![D_964]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_964)=k10_relat_1('#skF_9', D_964))), inference(resolution, [status(thm)], [c_46, c_21692])).
% 15.95/8.39  tff(c_68, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_85, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 15.95/8.39  tff(c_60, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_116, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_60])).
% 15.95/8.39  tff(c_64, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_154, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_64])).
% 15.95/8.39  tff(c_614, plain, (![A_224, B_225, C_226, D_227]: (k8_relset_1(A_224, B_225, C_226, D_227)=k10_relat_1(C_226, D_227) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 15.95/8.39  tff(c_625, plain, (![D_227]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_227)=k10_relat_1('#skF_9', D_227))), inference(resolution, [status(thm)], [c_46, c_614])).
% 15.95/8.39  tff(c_54, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_381, plain, (~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_54])).
% 15.95/8.39  tff(c_628, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_381])).
% 15.95/8.39  tff(c_22, plain, (![C_29, A_14, D_32]: (r2_hidden(C_29, k2_relat_1(A_14)) | ~r2_hidden(k4_tarski(D_32, C_29), A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.95/8.39  tff(c_164, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_154, c_22])).
% 15.95/8.39  tff(c_1476, plain, (![A_289, C_290, B_291, D_292]: (r2_hidden(A_289, k10_relat_1(C_290, B_291)) | ~r2_hidden(D_292, B_291) | ~r2_hidden(k4_tarski(A_289, D_292), C_290) | ~r2_hidden(D_292, k2_relat_1(C_290)) | ~v1_relat_1(C_290))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.95/8.39  tff(c_1729, plain, (![A_298, C_299]: (r2_hidden(A_298, k10_relat_1(C_299, '#skF_7')) | ~r2_hidden(k4_tarski(A_298, '#skF_11'), C_299) | ~r2_hidden('#skF_11', k2_relat_1(C_299)) | ~v1_relat_1(C_299))), inference(resolution, [status(thm)], [c_116, c_1476])).
% 15.95/8.39  tff(c_1803, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_11', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_154, c_1729])).
% 15.95/8.39  tff(c_1830, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_164, c_1803])).
% 15.95/8.39  tff(c_1832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_628, c_1830])).
% 15.95/8.39  tff(c_1842, plain, (![F_300]: (~r2_hidden(F_300, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_300), '#skF_9') | ~m1_subset_1(F_300, '#skF_8'))), inference(splitRight, [status(thm)], [c_54])).
% 15.95/8.39  tff(c_1849, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_154, c_1842])).
% 15.95/8.39  tff(c_1859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_116, c_1849])).
% 15.95/8.39  tff(c_1860, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 15.95/8.39  tff(c_21704, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_21699, c_1860])).
% 15.95/8.39  tff(c_48, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_40, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_5'(A_35, B_36, C_37), k2_relat_1(C_37)) | ~r2_hidden(A_35, k10_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.95/8.39  tff(c_21488, plain, (![A_933, C_934]: (r2_hidden(k4_tarski('#skF_4'(A_933, k2_relat_1(A_933), C_934), C_934), A_933) | ~r2_hidden(C_934, k2_relat_1(A_933)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.95/8.39  tff(c_16, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.95/8.39  tff(c_35128, plain, (![A_1352, C_1353, A_1354]: (r2_hidden(k4_tarski('#skF_4'(A_1352, k2_relat_1(A_1352), C_1353), C_1353), A_1354) | ~m1_subset_1(A_1352, k1_zfmisc_1(A_1354)) | ~r2_hidden(C_1353, k2_relat_1(A_1352)))), inference(resolution, [status(thm)], [c_21488, c_16])).
% 15.95/8.39  tff(c_35340, plain, (![C_1355, A_1356, A_1357]: (r2_hidden(C_1355, k2_relat_1(A_1356)) | ~m1_subset_1(A_1357, k1_zfmisc_1(A_1356)) | ~r2_hidden(C_1355, k2_relat_1(A_1357)))), inference(resolution, [status(thm)], [c_35128, c_22])).
% 15.95/8.39  tff(c_35360, plain, (![C_1358]: (r2_hidden(C_1358, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_1358, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_46, c_35340])).
% 15.95/8.39  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.95/8.39  tff(c_21506, plain, (![C_934, D_4, C_3]: (r2_hidden(C_934, D_4) | ~r2_hidden(C_934, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_21488, c_4])).
% 15.95/8.39  tff(c_35580, plain, (![C_1359]: (r2_hidden(C_1359, '#skF_8') | ~r2_hidden(C_1359, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_35360, c_21506])).
% 15.95/8.39  tff(c_35612, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k10_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_40, c_35580])).
% 15.95/8.39  tff(c_35668, plain, (![A_1362, B_1363]: (r2_hidden('#skF_5'(A_1362, B_1363, '#skF_9'), '#skF_8') | ~r2_hidden(A_1362, k10_relat_1('#skF_9', B_1363)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_35612])).
% 15.95/8.39  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.95/8.39  tff(c_35701, plain, (![A_1362, B_1363]: (m1_subset_1('#skF_5'(A_1362, B_1363, '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(A_1362, k10_relat_1('#skF_9', B_1363)))), inference(resolution, [status(thm)], [c_35668, c_8])).
% 15.95/8.39  tff(c_35720, plain, (![A_1364, B_1365]: (m1_subset_1('#skF_5'(A_1364, B_1365, '#skF_9'), '#skF_8') | ~r2_hidden(A_1364, k10_relat_1('#skF_9', B_1365)))), inference(negUnitSimplification, [status(thm)], [c_48, c_35701])).
% 15.95/8.39  tff(c_35777, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_21704, c_35720])).
% 15.95/8.39  tff(c_36, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_5'(A_35, B_36, C_37), B_36) | ~r2_hidden(A_35, k10_relat_1(C_37, B_36)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.95/8.39  tff(c_22147, plain, (![A_1022, B_1023, C_1024]: (r2_hidden(k4_tarski(A_1022, '#skF_5'(A_1022, B_1023, C_1024)), C_1024) | ~r2_hidden(A_1022, k10_relat_1(C_1024, B_1023)) | ~v1_relat_1(C_1024))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.95/8.39  tff(c_1861, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_64])).
% 15.95/8.39  tff(c_62, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_21726, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1861, c_62])).
% 15.95/8.39  tff(c_22158, plain, (![B_1023]: (~r2_hidden('#skF_5'('#skF_10', B_1023, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1023, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1023)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_22147, c_21726])).
% 15.95/8.39  tff(c_37215, plain, (![B_1404]: (~r2_hidden('#skF_5'('#skF_10', B_1404, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1404, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1404)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_22158])).
% 15.95/8.39  tff(c_37223, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_37215])).
% 15.95/8.39  tff(c_37233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_21704, c_35777, c_37223])).
% 15.95/8.39  tff(c_37234, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 15.95/8.39  tff(c_37451, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_37446, c_37234])).
% 15.95/8.39  tff(c_37278, plain, (![A_1420, C_1421]: (r2_hidden(k4_tarski('#skF_4'(A_1420, k2_relat_1(A_1420), C_1421), C_1421), A_1420) | ~r2_hidden(C_1421, k2_relat_1(A_1420)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.95/8.39  tff(c_45357, plain, (![A_1775, C_1776, A_1777]: (r2_hidden(k4_tarski('#skF_4'(A_1775, k2_relat_1(A_1775), C_1776), C_1776), A_1777) | ~m1_subset_1(A_1775, k1_zfmisc_1(A_1777)) | ~r2_hidden(C_1776, k2_relat_1(A_1775)))), inference(resolution, [status(thm)], [c_37278, c_16])).
% 15.95/8.39  tff(c_45537, plain, (![C_1778, A_1779, A_1780]: (r2_hidden(C_1778, k2_relat_1(A_1779)) | ~m1_subset_1(A_1780, k1_zfmisc_1(A_1779)) | ~r2_hidden(C_1778, k2_relat_1(A_1780)))), inference(resolution, [status(thm)], [c_45357, c_22])).
% 15.95/8.39  tff(c_45553, plain, (![C_1781]: (r2_hidden(C_1781, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_1781, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_46, c_45537])).
% 15.95/8.39  tff(c_37297, plain, (![C_1421, D_4, C_3]: (r2_hidden(C_1421, D_4) | ~r2_hidden(C_1421, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_37278, c_4])).
% 15.95/8.39  tff(c_45732, plain, (![C_1782]: (r2_hidden(C_1782, '#skF_8') | ~r2_hidden(C_1782, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_45553, c_37297])).
% 15.95/8.39  tff(c_45768, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k10_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_40, c_45732])).
% 15.95/8.39  tff(c_45825, plain, (![A_1785, B_1786]: (r2_hidden('#skF_5'(A_1785, B_1786, '#skF_9'), '#skF_8') | ~r2_hidden(A_1785, k10_relat_1('#skF_9', B_1786)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_45768])).
% 15.95/8.39  tff(c_45858, plain, (![A_1785, B_1786]: (m1_subset_1('#skF_5'(A_1785, B_1786, '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(A_1785, k10_relat_1('#skF_9', B_1786)))), inference(resolution, [status(thm)], [c_45825, c_8])).
% 15.95/8.39  tff(c_45877, plain, (![A_1787, B_1788]: (m1_subset_1('#skF_5'(A_1787, B_1788, '#skF_9'), '#skF_8') | ~r2_hidden(A_1787, k10_relat_1('#skF_9', B_1788)))), inference(negUnitSimplification, [status(thm)], [c_48, c_45858])).
% 15.95/8.39  tff(c_45932, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_37451, c_45877])).
% 15.95/8.39  tff(c_37743, plain, (![A_1491, B_1492, C_1493]: (r2_hidden(k4_tarski(A_1491, '#skF_5'(A_1491, B_1492, C_1493)), C_1493) | ~r2_hidden(A_1491, k10_relat_1(C_1493, B_1492)) | ~v1_relat_1(C_1493))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.95/8.39  tff(c_37235, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 15.95/8.39  tff(c_58, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_37409, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_37235, c_58])).
% 15.95/8.39  tff(c_37751, plain, (![B_1492]: (~r2_hidden('#skF_5'('#skF_10', B_1492, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1492, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1492)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_37743, c_37409])).
% 15.95/8.39  tff(c_46633, plain, (![B_1816]: (~r2_hidden('#skF_5'('#skF_10', B_1816, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1816, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1816)))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_37751])).
% 15.95/8.39  tff(c_46641, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_46633])).
% 15.95/8.39  tff(c_46651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_37451, c_45932, c_46641])).
% 15.95/8.39  tff(c_46652, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 15.95/8.39  tff(c_46842, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46839, c_46652])).
% 15.95/8.39  tff(c_47229, plain, (![A_1924, B_1925, C_1926]: (r2_hidden(k4_tarski(A_1924, '#skF_5'(A_1924, B_1925, C_1926)), C_1926) | ~r2_hidden(A_1924, k10_relat_1(C_1926, B_1925)) | ~v1_relat_1(C_1926))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.95/8.39  tff(c_46653, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 15.95/8.39  tff(c_66, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.95/8.39  tff(c_46735, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_133), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_46653, c_66])).
% 15.95/8.39  tff(c_47251, plain, (![B_1925]: (~r2_hidden('#skF_5'('#skF_10', B_1925, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1925, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1925)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_47229, c_46735])).
% 15.95/8.39  tff(c_48853, plain, (![B_2019]: (~r2_hidden('#skF_5'('#skF_10', B_2019, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_2019, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_2019)))), inference(demodulation, [status(thm), theory('equality')], [c_46680, c_47251])).
% 15.95/8.39  tff(c_48857, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_48853])).
% 15.95/8.39  tff(c_48863, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46680, c_46842, c_48857])).
% 15.95/8.39  tff(c_46742, plain, (![A_1848, C_1849]: (r2_hidden(k4_tarski('#skF_4'(A_1848, k2_relat_1(A_1848), C_1849), C_1849), A_1848) | ~r2_hidden(C_1849, k2_relat_1(A_1848)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.95/8.39  tff(c_56124, plain, (![A_2236, C_2237, A_2238]: (r2_hidden(k4_tarski('#skF_4'(A_2236, k2_relat_1(A_2236), C_2237), C_2237), A_2238) | ~m1_subset_1(A_2236, k1_zfmisc_1(A_2238)) | ~r2_hidden(C_2237, k2_relat_1(A_2236)))), inference(resolution, [status(thm)], [c_46742, c_16])).
% 15.95/8.39  tff(c_56325, plain, (![C_2239, A_2240, A_2241]: (r2_hidden(C_2239, k2_relat_1(A_2240)) | ~m1_subset_1(A_2241, k1_zfmisc_1(A_2240)) | ~r2_hidden(C_2239, k2_relat_1(A_2241)))), inference(resolution, [status(thm)], [c_56124, c_22])).
% 15.95/8.39  tff(c_56349, plain, (![C_2242]: (r2_hidden(C_2242, k2_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))) | ~r2_hidden(C_2242, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_46, c_56325])).
% 15.95/8.39  tff(c_46761, plain, (![C_1849, D_4, C_3]: (r2_hidden(C_1849, D_4) | ~r2_hidden(C_1849, k2_relat_1(k2_zfmisc_1(C_3, D_4))))), inference(resolution, [status(thm)], [c_46742, c_4])).
% 15.95/8.39  tff(c_56538, plain, (![C_2243]: (r2_hidden(C_2243, '#skF_8') | ~r2_hidden(C_2243, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_56349, c_46761])).
% 15.95/8.39  tff(c_56578, plain, (![A_35, B_36]: (r2_hidden('#skF_5'(A_35, B_36, '#skF_9'), '#skF_8') | ~r2_hidden(A_35, k10_relat_1('#skF_9', B_36)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_40, c_56538])).
% 15.95/8.39  tff(c_56636, plain, (![A_2246, B_2247]: (r2_hidden('#skF_5'(A_2246, B_2247, '#skF_9'), '#skF_8') | ~r2_hidden(A_2246, k10_relat_1('#skF_9', B_2247)))), inference(demodulation, [status(thm), theory('equality')], [c_46680, c_56578])).
% 15.95/8.39  tff(c_56673, plain, (![A_2246, B_2247]: (m1_subset_1('#skF_5'(A_2246, B_2247, '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(A_2246, k10_relat_1('#skF_9', B_2247)))), inference(resolution, [status(thm)], [c_56636, c_8])).
% 15.95/8.39  tff(c_56694, plain, (![A_2248, B_2249]: (m1_subset_1('#skF_5'(A_2248, B_2249, '#skF_9'), '#skF_8') | ~r2_hidden(A_2248, k10_relat_1('#skF_9', B_2249)))), inference(negUnitSimplification, [status(thm)], [c_48, c_56673])).
% 15.95/8.39  tff(c_56725, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_46842, c_56694])).
% 15.95/8.39  tff(c_56752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48863, c_56725])).
% 15.95/8.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.95/8.39  
% 15.95/8.39  Inference rules
% 15.95/8.39  ----------------------
% 15.95/8.39  #Ref     : 0
% 15.95/8.39  #Sup     : 15258
% 15.95/8.39  #Fact    : 0
% 15.95/8.39  #Define  : 0
% 15.95/8.39  #Split   : 62
% 15.95/8.39  #Chain   : 0
% 15.95/8.39  #Close   : 0
% 15.95/8.39  
% 15.95/8.39  Ordering : KBO
% 15.95/8.39  
% 15.95/8.39  Simplification rules
% 15.95/8.39  ----------------------
% 15.95/8.39  #Subsume      : 376
% 15.95/8.39  #Demod        : 163
% 15.95/8.39  #Tautology    : 264
% 15.95/8.39  #SimpNegUnit  : 85
% 15.95/8.39  #BackRed      : 22
% 15.95/8.39  
% 15.95/8.39  #Partial instantiations: 0
% 15.95/8.39  #Strategies tried      : 1
% 15.95/8.39  
% 15.95/8.39  Timing (in seconds)
% 15.95/8.39  ----------------------
% 15.95/8.39  Preprocessing        : 0.34
% 15.95/8.39  Parsing              : 0.17
% 15.95/8.39  CNF conversion       : 0.04
% 15.95/8.39  Main loop            : 7.22
% 15.95/8.39  Inferencing          : 1.27
% 15.95/8.39  Reduction            : 1.72
% 15.95/8.39  Demodulation         : 1.08
% 15.95/8.39  BG Simplification    : 0.30
% 15.95/8.39  Subsumption          : 3.22
% 15.95/8.39  Abstraction          : 0.32
% 15.95/8.39  MUC search           : 0.00
% 15.95/8.39  Cooper               : 0.00
% 15.95/8.39  Total                : 7.61
% 15.95/8.39  Index Insertion      : 0.00
% 15.95/8.39  Index Deletion       : 0.00
% 15.95/8.39  Index Matching       : 0.00
% 15.95/8.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
