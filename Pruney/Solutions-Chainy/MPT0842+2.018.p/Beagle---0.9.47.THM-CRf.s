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
% DateTime   : Thu Dec  3 10:08:38 EST 2020

% Result     : Theorem 16.06s
% Output     : CNFRefutation 16.06s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 301 expanded)
%              Number of leaves         :   33 ( 114 expanded)
%              Depth                    :    9
%              Number of atoms          :  245 ( 894 expanded)
%              Number of equality atoms :   10 (  25 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_115,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_71,axiom,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_51,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_38,plain,(
    ! [A_56,B_57] : v1_relat_1(k2_zfmisc_1(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26083,plain,(
    ! [B_1653,A_1654] :
      ( v1_relat_1(B_1653)
      | ~ m1_subset_1(B_1653,k1_zfmisc_1(A_1654))
      | ~ v1_relat_1(A_1654) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26090,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_52,c_26083])).

tff(c_26094,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26090])).

tff(c_26201,plain,(
    ! [A_1685,B_1686,C_1687,D_1688] :
      ( k8_relset_1(A_1685,B_1686,C_1687,D_1688) = k10_relat_1(C_1687,D_1688)
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(k2_zfmisc_1(A_1685,B_1686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26208,plain,(
    ! [D_1688] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_1688) = k10_relat_1('#skF_9',D_1688) ),
    inference(resolution,[status(thm)],[c_52,c_26201])).

tff(c_102,plain,(
    ! [B_167,A_168] :
      ( v1_relat_1(B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_168))
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_52,c_102])).

tff(c_113,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109])).

tff(c_5724,plain,(
    ! [A_794,B_795,C_796,D_797] :
      ( k8_relset_1(A_794,B_795,C_796,D_797) = k10_relat_1(C_796,D_797)
      | ~ m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1(A_794,B_795))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5731,plain,(
    ! [D_797] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_797) = k10_relat_1('#skF_9',D_797) ),
    inference(resolution,[status(thm)],[c_52,c_5724])).

tff(c_1441,plain,(
    ! [A_374,B_375,C_376,D_377] :
      ( k8_relset_1(A_374,B_375,C_376,D_377) = k10_relat_1(C_376,D_377)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(A_374,B_375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1448,plain,(
    ! [D_377] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_377) = k10_relat_1('#skF_9',D_377) ),
    inference(resolution,[status(thm)],[c_52,c_1441])).

tff(c_74,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_91,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_121,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_149,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_305,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k8_relset_1(A_209,B_210,C_211,D_212) = k10_relat_1(C_211,D_212)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_316,plain,(
    ! [D_212] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_212) = k10_relat_1('#skF_9',D_212) ),
    inference(resolution,[status(thm)],[c_52,c_305])).

tff(c_60,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_381,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_60])).

tff(c_382,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_393,plain,(
    ! [D_227,A_228,B_229,E_230] :
      ( r2_hidden(D_227,k10_relat_1(A_228,B_229))
      | ~ r2_hidden(E_230,B_229)
      | ~ r2_hidden(k4_tarski(D_227,E_230),A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_445,plain,(
    ! [D_235,A_236] :
      ( r2_hidden(D_235,k10_relat_1(A_236,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_235,'#skF_11'),A_236)
      | ~ v1_relat_1(A_236) ) ),
    inference(resolution,[status(thm)],[c_121,c_393])).

tff(c_455,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_149,c_445])).

tff(c_466,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_455])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_466])).

tff(c_478,plain,(
    ! [F_237] :
      ( ~ r2_hidden(F_237,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_237),'#skF_9')
      | ~ m1_subset_1(F_237,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_489,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_149,c_478])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_121,c_489])).

tff(c_503,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1452,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_503])).

tff(c_42,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_5'(A_58,B_59,C_60),B_59)
      | ~ r2_hidden(A_58,k10_relat_1(C_60,B_59))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden(k4_tarski(A_58,'#skF_5'(A_58,B_59,C_60)),C_60)
      | ~ r2_hidden(A_58,k10_relat_1(C_60,B_59))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_504,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1499,plain,(
    ! [F_382] :
      ( ~ r2_hidden(F_382,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_382),'#skF_9')
      | ~ m1_subset_1(F_382,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_68])).

tff(c_1503,plain,(
    ! [B_59] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_59,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_59,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_59))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_44,c_1499])).

tff(c_1740,plain,(
    ! [B_431] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_431,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_431,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_431)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1503])).

tff(c_1744,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_1740])).

tff(c_1750,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1452,c_1744])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1462,plain,(
    ! [A_379,B_380,C_381] :
      ( r2_hidden(k4_tarski(A_379,'#skF_5'(A_379,B_380,C_381)),C_381)
      | ~ r2_hidden(A_379,k10_relat_1(C_381,B_380))
      | ~ v1_relat_1(C_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3203,plain,(
    ! [A_600,B_601,C_602,A_603] :
      ( r2_hidden(k4_tarski(A_600,'#skF_5'(A_600,B_601,C_602)),A_603)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(A_603))
      | ~ r2_hidden(A_600,k10_relat_1(C_602,B_601))
      | ~ v1_relat_1(C_602) ) ),
    inference(resolution,[status(thm)],[c_1462,c_16])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5430,plain,(
    ! [D_764,C_767,C_763,A_765,B_766] :
      ( r2_hidden('#skF_5'(A_765,B_766,C_763),D_764)
      | ~ m1_subset_1(C_763,k1_zfmisc_1(k2_zfmisc_1(C_767,D_764)))
      | ~ r2_hidden(A_765,k10_relat_1(C_763,B_766))
      | ~ v1_relat_1(C_763) ) ),
    inference(resolution,[status(thm)],[c_3203,c_4])).

tff(c_5462,plain,(
    ! [A_765,B_766] :
      ( r2_hidden('#skF_5'(A_765,B_766,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_765,k10_relat_1('#skF_9',B_766))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_5430])).

tff(c_5476,plain,(
    ! [A_768,B_769] :
      ( r2_hidden('#skF_5'(A_768,B_769,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_768,k10_relat_1('#skF_9',B_769)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_5462])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5502,plain,(
    ! [A_768,B_769] :
      ( m1_subset_1('#skF_5'(A_768,B_769,'#skF_9'),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_768,k10_relat_1('#skF_9',B_769)) ) ),
    inference(resolution,[status(thm)],[c_5476,c_8])).

tff(c_5519,plain,(
    ! [A_770,B_771] :
      ( m1_subset_1('#skF_5'(A_770,B_771,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_770,k10_relat_1('#skF_9',B_771)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5502])).

tff(c_5594,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1452,c_5519])).

tff(c_5634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1750,c_5594])).

tff(c_5635,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5735,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5731,c_5635])).

tff(c_5759,plain,(
    ! [A_799,B_800,C_801] :
      ( r2_hidden(k4_tarski(A_799,'#skF_5'(A_799,B_800,C_801)),C_801)
      | ~ r2_hidden(A_799,k10_relat_1(C_801,B_800))
      | ~ v1_relat_1(C_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5636,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5717,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5636,c_64])).

tff(c_5763,plain,(
    ! [B_800] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_800,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_800,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_800))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5759,c_5717])).

tff(c_5911,plain,(
    ! [B_834] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_834,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_834,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_834)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_5763])).

tff(c_5915,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_5911])).

tff(c_5921,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_5735,c_5915])).

tff(c_7008,plain,(
    ! [A_977,B_978,C_979,A_980] :
      ( r2_hidden(k4_tarski(A_977,'#skF_5'(A_977,B_978,C_979)),A_980)
      | ~ m1_subset_1(C_979,k1_zfmisc_1(A_980))
      | ~ r2_hidden(A_977,k10_relat_1(C_979,B_978))
      | ~ v1_relat_1(C_979) ) ),
    inference(resolution,[status(thm)],[c_5759,c_16])).

tff(c_25311,plain,(
    ! [A_1643,D_1642,C_1644,C_1640,B_1641] :
      ( r2_hidden('#skF_5'(A_1643,B_1641,C_1640),D_1642)
      | ~ m1_subset_1(C_1640,k1_zfmisc_1(k2_zfmisc_1(C_1644,D_1642)))
      | ~ r2_hidden(A_1643,k10_relat_1(C_1640,B_1641))
      | ~ v1_relat_1(C_1640) ) ),
    inference(resolution,[status(thm)],[c_7008,c_4])).

tff(c_25391,plain,(
    ! [A_1643,B_1641] :
      ( r2_hidden('#skF_5'(A_1643,B_1641,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1643,k10_relat_1('#skF_9',B_1641))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_25311])).

tff(c_25433,plain,(
    ! [A_1645,B_1646] :
      ( r2_hidden('#skF_5'(A_1645,B_1646,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1645,k10_relat_1('#skF_9',B_1646)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_25391])).

tff(c_25483,plain,(
    ! [A_1645,B_1646] :
      ( m1_subset_1('#skF_5'(A_1645,B_1646,'#skF_9'),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_1645,k10_relat_1('#skF_9',B_1646)) ) ),
    inference(resolution,[status(thm)],[c_25433,c_8])).

tff(c_25766,plain,(
    ! [A_1649,B_1650] :
      ( m1_subset_1('#skF_5'(A_1649,B_1650,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_1649,k10_relat_1('#skF_9',B_1650)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_25483])).

tff(c_25974,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_5735,c_25766])).

tff(c_26074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5921,c_25974])).

tff(c_26075,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_26213,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26208,c_26075])).

tff(c_26332,plain,(
    ! [A_1712,B_1713,C_1714] :
      ( r2_hidden(k4_tarski(A_1712,'#skF_5'(A_1712,B_1713,C_1714)),C_1714)
      | ~ r2_hidden(A_1712,k10_relat_1(C_1714,B_1713))
      | ~ v1_relat_1(C_1714) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26076,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26156,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26076,c_72])).

tff(c_26338,plain,(
    ! [B_1713] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1713,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1713,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1713))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_26332,c_26156])).

tff(c_26539,plain,(
    ! [B_1753] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_1753,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_1753,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_1753)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26094,c_26338])).

tff(c_26547,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_26539])).

tff(c_26556,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26094,c_26213,c_26547])).

tff(c_27781,plain,(
    ! [A_1890,B_1891,C_1892,A_1893] :
      ( r2_hidden(k4_tarski(A_1890,'#skF_5'(A_1890,B_1891,C_1892)),A_1893)
      | ~ m1_subset_1(C_1892,k1_zfmisc_1(A_1893))
      | ~ r2_hidden(A_1890,k10_relat_1(C_1892,B_1891))
      | ~ v1_relat_1(C_1892) ) ),
    inference(resolution,[status(thm)],[c_26332,c_16])).

tff(c_41574,plain,(
    ! [D_2429,C_2426,A_2428,B_2427,C_2430] :
      ( r2_hidden('#skF_5'(A_2428,B_2427,C_2426),D_2429)
      | ~ m1_subset_1(C_2426,k1_zfmisc_1(k2_zfmisc_1(C_2430,D_2429)))
      | ~ r2_hidden(A_2428,k10_relat_1(C_2426,B_2427))
      | ~ v1_relat_1(C_2426) ) ),
    inference(resolution,[status(thm)],[c_27781,c_4])).

tff(c_41642,plain,(
    ! [A_2428,B_2427] :
      ( r2_hidden('#skF_5'(A_2428,B_2427,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_2428,k10_relat_1('#skF_9',B_2427))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_41574])).

tff(c_41678,plain,(
    ! [A_2431,B_2432] :
      ( r2_hidden('#skF_5'(A_2431,B_2432,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_2431,k10_relat_1('#skF_9',B_2432)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26094,c_41642])).

tff(c_41722,plain,(
    ! [A_2431,B_2432] :
      ( m1_subset_1('#skF_5'(A_2431,B_2432,'#skF_9'),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_2431,k10_relat_1('#skF_9',B_2432)) ) ),
    inference(resolution,[status(thm)],[c_41678,c_8])).

tff(c_41752,plain,(
    ! [A_2433,B_2434] :
      ( m1_subset_1('#skF_5'(A_2433,B_2434,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_2433,k10_relat_1('#skF_9',B_2434)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_41722])).

tff(c_41929,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_26213,c_41752])).

tff(c_42013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26556,c_41929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.06/8.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.06/8.40  
% 16.06/8.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.06/8.40  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 16.06/8.40  
% 16.06/8.40  %Foreground sorts:
% 16.06/8.40  
% 16.06/8.40  
% 16.06/8.40  %Background operators:
% 16.06/8.40  
% 16.06/8.40  
% 16.06/8.40  %Foreground operators:
% 16.06/8.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.06/8.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.06/8.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.06/8.40  tff('#skF_11', type, '#skF_11': $i).
% 16.06/8.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.06/8.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 16.06/8.40  tff('#skF_7', type, '#skF_7': $i).
% 16.06/8.40  tff('#skF_10', type, '#skF_10': $i).
% 16.06/8.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.06/8.40  tff('#skF_6', type, '#skF_6': $i).
% 16.06/8.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 16.06/8.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.06/8.40  tff('#skF_9', type, '#skF_9': $i).
% 16.06/8.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.06/8.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 16.06/8.40  tff('#skF_8', type, '#skF_8': $i).
% 16.06/8.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.06/8.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 16.06/8.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.06/8.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.06/8.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.06/8.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.06/8.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.06/8.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.06/8.40  
% 16.06/8.43  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 16.06/8.43  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 16.06/8.43  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 16.06/8.43  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 16.06/8.43  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 16.06/8.43  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 16.06/8.43  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 16.06/8.43  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 16.06/8.43  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 16.06/8.43  tff(c_38, plain, (![A_56, B_57]: (v1_relat_1(k2_zfmisc_1(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.06/8.43  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_26083, plain, (![B_1653, A_1654]: (v1_relat_1(B_1653) | ~m1_subset_1(B_1653, k1_zfmisc_1(A_1654)) | ~v1_relat_1(A_1654))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.06/8.43  tff(c_26090, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_26083])).
% 16.06/8.43  tff(c_26094, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26090])).
% 16.06/8.43  tff(c_26201, plain, (![A_1685, B_1686, C_1687, D_1688]: (k8_relset_1(A_1685, B_1686, C_1687, D_1688)=k10_relat_1(C_1687, D_1688) | ~m1_subset_1(C_1687, k1_zfmisc_1(k2_zfmisc_1(A_1685, B_1686))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.06/8.43  tff(c_26208, plain, (![D_1688]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_1688)=k10_relat_1('#skF_9', D_1688))), inference(resolution, [status(thm)], [c_52, c_26201])).
% 16.06/8.43  tff(c_102, plain, (![B_167, A_168]: (v1_relat_1(B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_168)) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.06/8.43  tff(c_109, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_102])).
% 16.06/8.43  tff(c_113, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109])).
% 16.06/8.43  tff(c_5724, plain, (![A_794, B_795, C_796, D_797]: (k8_relset_1(A_794, B_795, C_796, D_797)=k10_relat_1(C_796, D_797) | ~m1_subset_1(C_796, k1_zfmisc_1(k2_zfmisc_1(A_794, B_795))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.06/8.43  tff(c_5731, plain, (![D_797]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_797)=k10_relat_1('#skF_9', D_797))), inference(resolution, [status(thm)], [c_52, c_5724])).
% 16.06/8.43  tff(c_1441, plain, (![A_374, B_375, C_376, D_377]: (k8_relset_1(A_374, B_375, C_376, D_377)=k10_relat_1(C_376, D_377) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(A_374, B_375))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.06/8.43  tff(c_1448, plain, (![D_377]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_377)=k10_relat_1('#skF_9', D_377))), inference(resolution, [status(thm)], [c_52, c_1441])).
% 16.06/8.43  tff(c_74, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_91, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_74])).
% 16.06/8.43  tff(c_66, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_121, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_66])).
% 16.06/8.43  tff(c_70, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_149, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_70])).
% 16.06/8.43  tff(c_305, plain, (![A_209, B_210, C_211, D_212]: (k8_relset_1(A_209, B_210, C_211, D_212)=k10_relat_1(C_211, D_212) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.06/8.43  tff(c_316, plain, (![D_212]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_212)=k10_relat_1('#skF_9', D_212))), inference(resolution, [status(thm)], [c_52, c_305])).
% 16.06/8.43  tff(c_60, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_381, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_60])).
% 16.06/8.43  tff(c_382, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_381])).
% 16.06/8.43  tff(c_393, plain, (![D_227, A_228, B_229, E_230]: (r2_hidden(D_227, k10_relat_1(A_228, B_229)) | ~r2_hidden(E_230, B_229) | ~r2_hidden(k4_tarski(D_227, E_230), A_228) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.06/8.43  tff(c_445, plain, (![D_235, A_236]: (r2_hidden(D_235, k10_relat_1(A_236, '#skF_7')) | ~r2_hidden(k4_tarski(D_235, '#skF_11'), A_236) | ~v1_relat_1(A_236))), inference(resolution, [status(thm)], [c_121, c_393])).
% 16.06/8.43  tff(c_455, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_149, c_445])).
% 16.06/8.43  tff(c_466, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_455])).
% 16.06/8.43  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_466])).
% 16.06/8.43  tff(c_478, plain, (![F_237]: (~r2_hidden(F_237, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_237), '#skF_9') | ~m1_subset_1(F_237, '#skF_8'))), inference(splitRight, [status(thm)], [c_381])).
% 16.06/8.43  tff(c_489, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_149, c_478])).
% 16.06/8.43  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_121, c_489])).
% 16.06/8.43  tff(c_503, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_70])).
% 16.06/8.43  tff(c_1452, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_503])).
% 16.06/8.43  tff(c_42, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_5'(A_58, B_59, C_60), B_59) | ~r2_hidden(A_58, k10_relat_1(C_60, B_59)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.06/8.43  tff(c_44, plain, (![A_58, B_59, C_60]: (r2_hidden(k4_tarski(A_58, '#skF_5'(A_58, B_59, C_60)), C_60) | ~r2_hidden(A_58, k10_relat_1(C_60, B_59)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.06/8.43  tff(c_504, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 16.06/8.43  tff(c_68, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_1499, plain, (![F_382]: (~r2_hidden(F_382, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_382), '#skF_9') | ~m1_subset_1(F_382, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_504, c_68])).
% 16.06/8.43  tff(c_1503, plain, (![B_59]: (~r2_hidden('#skF_5'('#skF_10', B_59, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_59, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_59)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_44, c_1499])).
% 16.06/8.43  tff(c_1740, plain, (![B_431]: (~r2_hidden('#skF_5'('#skF_10', B_431, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_431, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_431)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1503])).
% 16.06/8.43  tff(c_1744, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_1740])).
% 16.06/8.43  tff(c_1750, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1452, c_1744])).
% 16.06/8.43  tff(c_54, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_1462, plain, (![A_379, B_380, C_381]: (r2_hidden(k4_tarski(A_379, '#skF_5'(A_379, B_380, C_381)), C_381) | ~r2_hidden(A_379, k10_relat_1(C_381, B_380)) | ~v1_relat_1(C_381))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.06/8.43  tff(c_16, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 16.06/8.43  tff(c_3203, plain, (![A_600, B_601, C_602, A_603]: (r2_hidden(k4_tarski(A_600, '#skF_5'(A_600, B_601, C_602)), A_603) | ~m1_subset_1(C_602, k1_zfmisc_1(A_603)) | ~r2_hidden(A_600, k10_relat_1(C_602, B_601)) | ~v1_relat_1(C_602))), inference(resolution, [status(thm)], [c_1462, c_16])).
% 16.06/8.43  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.06/8.43  tff(c_5430, plain, (![D_764, C_767, C_763, A_765, B_766]: (r2_hidden('#skF_5'(A_765, B_766, C_763), D_764) | ~m1_subset_1(C_763, k1_zfmisc_1(k2_zfmisc_1(C_767, D_764))) | ~r2_hidden(A_765, k10_relat_1(C_763, B_766)) | ~v1_relat_1(C_763))), inference(resolution, [status(thm)], [c_3203, c_4])).
% 16.06/8.43  tff(c_5462, plain, (![A_765, B_766]: (r2_hidden('#skF_5'(A_765, B_766, '#skF_9'), '#skF_8') | ~r2_hidden(A_765, k10_relat_1('#skF_9', B_766)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_5430])).
% 16.06/8.43  tff(c_5476, plain, (![A_768, B_769]: (r2_hidden('#skF_5'(A_768, B_769, '#skF_9'), '#skF_8') | ~r2_hidden(A_768, k10_relat_1('#skF_9', B_769)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_5462])).
% 16.06/8.43  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.06/8.43  tff(c_5502, plain, (![A_768, B_769]: (m1_subset_1('#skF_5'(A_768, B_769, '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(A_768, k10_relat_1('#skF_9', B_769)))), inference(resolution, [status(thm)], [c_5476, c_8])).
% 16.06/8.43  tff(c_5519, plain, (![A_770, B_771]: (m1_subset_1('#skF_5'(A_770, B_771, '#skF_9'), '#skF_8') | ~r2_hidden(A_770, k10_relat_1('#skF_9', B_771)))), inference(negUnitSimplification, [status(thm)], [c_54, c_5502])).
% 16.06/8.43  tff(c_5594, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1452, c_5519])).
% 16.06/8.43  tff(c_5634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1750, c_5594])).
% 16.06/8.43  tff(c_5635, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 16.06/8.43  tff(c_5735, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_5731, c_5635])).
% 16.06/8.43  tff(c_5759, plain, (![A_799, B_800, C_801]: (r2_hidden(k4_tarski(A_799, '#skF_5'(A_799, B_800, C_801)), C_801) | ~r2_hidden(A_799, k10_relat_1(C_801, B_800)) | ~v1_relat_1(C_801))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.06/8.43  tff(c_5636, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_66])).
% 16.06/8.43  tff(c_64, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_5717, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_5636, c_64])).
% 16.06/8.43  tff(c_5763, plain, (![B_800]: (~r2_hidden('#skF_5'('#skF_10', B_800, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_800, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_800)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_5759, c_5717])).
% 16.06/8.43  tff(c_5911, plain, (![B_834]: (~r2_hidden('#skF_5'('#skF_10', B_834, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_834, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_834)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_5763])).
% 16.06/8.43  tff(c_5915, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_5911])).
% 16.06/8.43  tff(c_5921, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_5735, c_5915])).
% 16.06/8.43  tff(c_7008, plain, (![A_977, B_978, C_979, A_980]: (r2_hidden(k4_tarski(A_977, '#skF_5'(A_977, B_978, C_979)), A_980) | ~m1_subset_1(C_979, k1_zfmisc_1(A_980)) | ~r2_hidden(A_977, k10_relat_1(C_979, B_978)) | ~v1_relat_1(C_979))), inference(resolution, [status(thm)], [c_5759, c_16])).
% 16.06/8.43  tff(c_25311, plain, (![A_1643, D_1642, C_1644, C_1640, B_1641]: (r2_hidden('#skF_5'(A_1643, B_1641, C_1640), D_1642) | ~m1_subset_1(C_1640, k1_zfmisc_1(k2_zfmisc_1(C_1644, D_1642))) | ~r2_hidden(A_1643, k10_relat_1(C_1640, B_1641)) | ~v1_relat_1(C_1640))), inference(resolution, [status(thm)], [c_7008, c_4])).
% 16.06/8.43  tff(c_25391, plain, (![A_1643, B_1641]: (r2_hidden('#skF_5'(A_1643, B_1641, '#skF_9'), '#skF_8') | ~r2_hidden(A_1643, k10_relat_1('#skF_9', B_1641)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_25311])).
% 16.06/8.43  tff(c_25433, plain, (![A_1645, B_1646]: (r2_hidden('#skF_5'(A_1645, B_1646, '#skF_9'), '#skF_8') | ~r2_hidden(A_1645, k10_relat_1('#skF_9', B_1646)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_25391])).
% 16.06/8.43  tff(c_25483, plain, (![A_1645, B_1646]: (m1_subset_1('#skF_5'(A_1645, B_1646, '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(A_1645, k10_relat_1('#skF_9', B_1646)))), inference(resolution, [status(thm)], [c_25433, c_8])).
% 16.06/8.43  tff(c_25766, plain, (![A_1649, B_1650]: (m1_subset_1('#skF_5'(A_1649, B_1650, '#skF_9'), '#skF_8') | ~r2_hidden(A_1649, k10_relat_1('#skF_9', B_1650)))), inference(negUnitSimplification, [status(thm)], [c_54, c_25483])).
% 16.06/8.43  tff(c_25974, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_5735, c_25766])).
% 16.06/8.43  tff(c_26074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5921, c_25974])).
% 16.06/8.43  tff(c_26075, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_74])).
% 16.06/8.43  tff(c_26213, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_26208, c_26075])).
% 16.06/8.43  tff(c_26332, plain, (![A_1712, B_1713, C_1714]: (r2_hidden(k4_tarski(A_1712, '#skF_5'(A_1712, B_1713, C_1714)), C_1714) | ~r2_hidden(A_1712, k10_relat_1(C_1714, B_1713)) | ~v1_relat_1(C_1714))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.06/8.43  tff(c_26076, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_74])).
% 16.06/8.43  tff(c_72, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.06/8.43  tff(c_26156, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_26076, c_72])).
% 16.06/8.43  tff(c_26338, plain, (![B_1713]: (~r2_hidden('#skF_5'('#skF_10', B_1713, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1713, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1713)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_26332, c_26156])).
% 16.06/8.43  tff(c_26539, plain, (![B_1753]: (~r2_hidden('#skF_5'('#skF_10', B_1753, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_1753, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_1753)))), inference(demodulation, [status(thm), theory('equality')], [c_26094, c_26338])).
% 16.06/8.43  tff(c_26547, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_26539])).
% 16.06/8.43  tff(c_26556, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26094, c_26213, c_26547])).
% 16.06/8.43  tff(c_27781, plain, (![A_1890, B_1891, C_1892, A_1893]: (r2_hidden(k4_tarski(A_1890, '#skF_5'(A_1890, B_1891, C_1892)), A_1893) | ~m1_subset_1(C_1892, k1_zfmisc_1(A_1893)) | ~r2_hidden(A_1890, k10_relat_1(C_1892, B_1891)) | ~v1_relat_1(C_1892))), inference(resolution, [status(thm)], [c_26332, c_16])).
% 16.06/8.43  tff(c_41574, plain, (![D_2429, C_2426, A_2428, B_2427, C_2430]: (r2_hidden('#skF_5'(A_2428, B_2427, C_2426), D_2429) | ~m1_subset_1(C_2426, k1_zfmisc_1(k2_zfmisc_1(C_2430, D_2429))) | ~r2_hidden(A_2428, k10_relat_1(C_2426, B_2427)) | ~v1_relat_1(C_2426))), inference(resolution, [status(thm)], [c_27781, c_4])).
% 16.06/8.43  tff(c_41642, plain, (![A_2428, B_2427]: (r2_hidden('#skF_5'(A_2428, B_2427, '#skF_9'), '#skF_8') | ~r2_hidden(A_2428, k10_relat_1('#skF_9', B_2427)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_41574])).
% 16.06/8.43  tff(c_41678, plain, (![A_2431, B_2432]: (r2_hidden('#skF_5'(A_2431, B_2432, '#skF_9'), '#skF_8') | ~r2_hidden(A_2431, k10_relat_1('#skF_9', B_2432)))), inference(demodulation, [status(thm), theory('equality')], [c_26094, c_41642])).
% 16.06/8.43  tff(c_41722, plain, (![A_2431, B_2432]: (m1_subset_1('#skF_5'(A_2431, B_2432, '#skF_9'), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(A_2431, k10_relat_1('#skF_9', B_2432)))), inference(resolution, [status(thm)], [c_41678, c_8])).
% 16.06/8.43  tff(c_41752, plain, (![A_2433, B_2434]: (m1_subset_1('#skF_5'(A_2433, B_2434, '#skF_9'), '#skF_8') | ~r2_hidden(A_2433, k10_relat_1('#skF_9', B_2434)))), inference(negUnitSimplification, [status(thm)], [c_54, c_41722])).
% 16.06/8.43  tff(c_41929, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_26213, c_41752])).
% 16.06/8.43  tff(c_42013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26556, c_41929])).
% 16.06/8.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.06/8.43  
% 16.06/8.43  Inference rules
% 16.06/8.43  ----------------------
% 16.06/8.43  #Ref     : 0
% 16.06/8.43  #Sup     : 9936
% 16.06/8.43  #Fact    : 0
% 16.06/8.43  #Define  : 0
% 16.06/8.43  #Split   : 149
% 16.06/8.43  #Chain   : 0
% 16.06/8.43  #Close   : 0
% 16.06/8.43  
% 16.06/8.43  Ordering : KBO
% 16.06/8.43  
% 16.06/8.43  Simplification rules
% 16.06/8.43  ----------------------
% 16.06/8.43  #Subsume      : 1047
% 16.06/8.43  #Demod        : 1322
% 16.06/8.43  #Tautology    : 447
% 16.06/8.43  #SimpNegUnit  : 555
% 16.06/8.43  #BackRed      : 94
% 16.06/8.43  
% 16.06/8.43  #Partial instantiations: 0
% 16.06/8.43  #Strategies tried      : 1
% 16.06/8.43  
% 16.06/8.43  Timing (in seconds)
% 16.06/8.43  ----------------------
% 16.06/8.43  Preprocessing        : 0.34
% 16.06/8.43  Parsing              : 0.16
% 16.06/8.43  CNF conversion       : 0.04
% 16.06/8.43  Main loop            : 7.31
% 16.06/8.43  Inferencing          : 1.57
% 16.06/8.43  Reduction            : 1.92
% 16.06/8.43  Demodulation         : 1.27
% 16.06/8.43  BG Simplification    : 0.22
% 16.06/8.43  Subsumption          : 2.97
% 16.06/8.43  Abstraction          : 0.28
% 16.06/8.43  MUC search           : 0.00
% 16.06/8.43  Cooper               : 0.00
% 16.06/8.43  Total                : 7.69
% 16.06/8.43  Index Insertion      : 0.00
% 16.06/8.43  Index Deletion       : 0.00
% 16.06/8.43  Index Matching       : 0.00
% 16.06/8.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
