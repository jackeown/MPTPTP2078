%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:54 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 396 expanded)
%              Number of leaves         :   34 ( 136 expanded)
%              Depth                    :    9
%              Number of atoms          :  268 ( 885 expanded)
%              Number of equality atoms :   58 ( 144 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_46,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1990,plain,(
    ! [B_238,A_239] :
      ( v1_xboole_0(B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_239))
      | ~ v1_xboole_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2005,plain,(
    ! [A_15] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_1990])).

tff(c_2006,plain,(
    ! [A_15] : ~ v1_xboole_0(A_15) ),
    inference(splitLeft,[status(thm)],[c_2005])).

tff(c_14,plain,(
    ! [A_10] : v1_xboole_0('#skF_2'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2006,c_14])).

tff(c_2010,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2005])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden('#skF_1'(A_56,B_57),B_57)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1512,plain,(
    ! [A_201,B_202] :
      ( r2_hidden('#skF_3'(A_201,B_202),B_202)
      | k1_xboole_0 = B_202
      | ~ m1_subset_1(B_202,k1_zfmisc_1(A_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1574,plain,(
    ! [B_205,A_206] :
      ( ~ v1_xboole_0(B_205)
      | k1_xboole_0 = B_205
      | ~ m1_subset_1(B_205,k1_zfmisc_1(A_206)) ) ),
    inference(resolution,[status(thm)],[c_1512,c_8])).

tff(c_1603,plain,
    ( ~ v1_xboole_0('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_1574])).

tff(c_1627,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1603])).

tff(c_1377,plain,(
    ! [A_181,B_182] :
      ( k6_setfam_1(A_181,B_182) = k1_setfam_1(B_182)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k1_zfmisc_1(A_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1394,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_1377])).

tff(c_1718,plain,(
    ! [A_217,B_218] :
      ( k8_setfam_1(A_217,B_218) = k6_setfam_1(A_217,B_218)
      | k1_xboole_0 = B_218
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k1_zfmisc_1(A_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1729,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_1718])).

tff(c_1737,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_1729])).

tff(c_1741,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1737])).

tff(c_82,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    ! [A_15] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_96,plain,(
    ! [A_15] : ~ v1_xboole_0(A_15) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_14])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_1758,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1741,c_101])).

tff(c_1762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_1758])).

tff(c_1763,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1778,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1763,c_75])).

tff(c_1764,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_1544,plain,(
    ! [A_203,B_204] :
      ( r2_hidden('#skF_4'(A_203,B_204),A_203)
      | r1_tarski(B_204,k1_setfam_1(A_203))
      | k1_xboole_0 = A_203 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    ! [D_33] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_132,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_121,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_199,plain,(
    ! [D_68] :
      ( r2_hidden('#skF_6',D_68)
      | ~ r2_hidden(D_68,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_54])).

tff(c_204,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_121,c_199])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_204])).

tff(c_214,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_218,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_214,c_8])).

tff(c_463,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_3'(A_95,B_96),B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_213,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_485,plain,(
    ! [A_95] :
      ( r2_hidden('#skF_6','#skF_3'(A_95,'#skF_7'))
      | k1_xboole_0 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_463,c_213])).

tff(c_709,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_234,plain,(
    ! [C_72,B_73,A_74] :
      ( r2_hidden(C_72,B_73)
      | ~ r2_hidden(C_72,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_247,plain,(
    ! [B_73] :
      ( r2_hidden('#skF_8',B_73)
      | ~ r1_tarski('#skF_7',B_73) ) ),
    inference(resolution,[status(thm)],[c_121,c_234])).

tff(c_392,plain,(
    ! [A_87,C_88,B_89] :
      ( m1_subset_1(A_87,C_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(C_88))
      | ~ r2_hidden(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_402,plain,(
    ! [A_90,A_91] :
      ( m1_subset_1(A_90,A_91)
      | ~ r2_hidden(A_90,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_392])).

tff(c_416,plain,(
    ! [A_91] :
      ( m1_subset_1('#skF_8',A_91)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_247,c_402])).

tff(c_432,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_718,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_432])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_718])).

tff(c_729,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_338,plain,(
    ! [A_81,B_82] :
      ( k6_setfam_1(A_81,B_82) = k1_setfam_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_350,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_338])).

tff(c_959,plain,(
    ! [A_140,B_141] :
      ( k8_setfam_1(A_140,B_141) = k6_setfam_1(A_140,B_141)
      | k1_xboole_0 = B_141
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k1_zfmisc_1(A_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_970,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_959])).

tff(c_978,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_970])).

tff(c_979,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_978])).

tff(c_985,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_75])).

tff(c_825,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_4'(A_131,B_132),A_131)
      | r1_tarski(B_132,k1_setfam_1(A_131))
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_843,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_6','#skF_4'('#skF_7',B_132))
      | r1_tarski(B_132,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_825,c_213])).

tff(c_859,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_6','#skF_4'('#skF_7',B_132))
      | r1_tarski(B_132,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_843])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_768,plain,(
    ! [B_121,A_122] :
      ( ~ r1_tarski(B_121,'#skF_4'(A_122,B_121))
      | r1_tarski(B_121,k1_setfam_1(A_122))
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1148,plain,(
    ! [A_154,A_155] :
      ( r1_tarski(k1_tarski(A_154),k1_setfam_1(A_155))
      | k1_xboole_0 = A_155
      | ~ r2_hidden(A_154,'#skF_4'(A_155,k1_tarski(A_154))) ) ),
    inference(resolution,[status(thm)],[c_12,c_768])).

tff(c_1156,plain,
    ( k1_xboole_0 = '#skF_7'
    | r1_tarski(k1_tarski('#skF_6'),k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_859,c_1148])).

tff(c_1172,plain,(
    r1_tarski(k1_tarski('#skF_6'),k1_setfam_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_1156])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | ~ r1_tarski(k1_tarski(A_8),B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1186,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1172,c_10])).

tff(c_1198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_985,c_1186])).

tff(c_1201,plain,(
    ! [A_156] : m1_subset_1('#skF_8',A_156) ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_24,plain,(
    ! [B_18,A_16] :
      ( v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_16))
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1212,plain,(
    ! [A_16] :
      ( v1_xboole_0('#skF_8')
      | ~ v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_1201,c_24])).

tff(c_1217,plain,(
    ! [A_16] : ~ v1_xboole_0(A_16) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1212])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1217,c_101])).

tff(c_1222,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1572,plain,(
    ! [B_204] :
      ( r2_hidden('#skF_6','#skF_4'('#skF_7',B_204))
      | r1_tarski(B_204,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1544,c_1222])).

tff(c_1765,plain,(
    ! [B_204] :
      ( r2_hidden('#skF_6','#skF_4'('#skF_7',B_204))
      | r1_tarski(B_204,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1764,c_1572])).

tff(c_1499,plain,(
    ! [B_199,A_200] :
      ( ~ r1_tarski(B_199,'#skF_4'(A_200,B_199))
      | r1_tarski(B_199,k1_setfam_1(A_200))
      | k1_xboole_0 = A_200 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1879,plain,(
    ! [A_229,A_230] :
      ( r1_tarski(k1_tarski(A_229),k1_setfam_1(A_230))
      | k1_xboole_0 = A_230
      | ~ r2_hidden(A_229,'#skF_4'(A_230,k1_tarski(A_229))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1499])).

tff(c_1883,plain,
    ( k1_xboole_0 = '#skF_7'
    | r1_tarski(k1_tarski('#skF_6'),k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1765,c_1879])).

tff(c_1894,plain,(
    r1_tarski(k1_tarski('#skF_6'),k1_setfam_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_1764,c_1883])).

tff(c_1903,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1894,c_10])).

tff(c_1911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_1903])).

tff(c_1912,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1603])).

tff(c_26,plain,(
    ! [A_19] :
      ( k8_setfam_1(A_19,k1_xboole_0) = A_19
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_19] : k8_setfam_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_1927,plain,(
    ! [A_19] : k8_setfam_1(A_19,'#skF_7') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1912,c_56])).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1248,plain,(
    ! [C_163,B_164,A_165] :
      ( r2_hidden(C_163,B_164)
      | ~ r2_hidden(C_163,A_165)
      | ~ r1_tarski(A_165,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1262,plain,(
    ! [B_166] :
      ( r2_hidden('#skF_6',B_166)
      | ~ r1_tarski('#skF_5',B_166) ) ),
    inference(resolution,[status(thm)],[c_40,c_1248])).

tff(c_1280,plain,(
    ~ r1_tarski('#skF_5',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1262,c_75])).

tff(c_1967,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1280])).

tff(c_1971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1967])).

tff(c_1972,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2012,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_1'(A_242,B_243),A_242)
      | r1_tarski(A_242,B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2020,plain,(
    ! [A_242] : r1_tarski(A_242,A_242) ),
    inference(resolution,[status(thm)],[c_2012,c_4])).

tff(c_1973,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1985,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_46])).

tff(c_2041,plain,(
    ! [C_249,B_250,A_251] :
      ( r2_hidden(C_249,B_250)
      | ~ r2_hidden(C_249,A_251)
      | ~ r1_tarski(A_251,B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2054,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_8',B_250)
      | ~ r1_tarski('#skF_7',B_250) ) ),
    inference(resolution,[status(thm)],[c_1985,c_2041])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2142,plain,(
    ! [A_261,B_262] :
      ( k6_setfam_1(A_261,B_262) = k1_setfam_1(B_262)
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k1_zfmisc_1(A_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2154,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_2142])).

tff(c_2592,plain,(
    ! [A_304,B_305] :
      ( k8_setfam_1(A_304,B_305) = k6_setfam_1(A_304,B_305)
      | k1_xboole_0 = B_305
      | ~ m1_subset_1(B_305,k1_zfmisc_1(k1_zfmisc_1(A_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2603,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_2592])).

tff(c_2611,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_2603])).

tff(c_2615,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2611])).

tff(c_2157,plain,(
    ! [A_263,C_264,B_265] :
      ( m1_subset_1(A_263,C_264)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(C_264))
      | ~ r2_hidden(A_263,B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2178,plain,(
    ! [A_267,A_268] :
      ( m1_subset_1(A_267,A_268)
      | ~ r2_hidden(A_267,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_2157])).

tff(c_2189,plain,(
    ! [A_268] :
      ( m1_subset_1('#skF_8',A_268)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2054,c_2178])).

tff(c_2204,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2189])).

tff(c_2628,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_2204])).

tff(c_2637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_2628])).

tff(c_2638,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2611])).

tff(c_2055,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_6',B_250)
      | ~ r1_tarski(k8_setfam_1('#skF_5','#skF_7'),B_250) ) ),
    inference(resolution,[status(thm)],[c_1973,c_2041])).

tff(c_2658,plain,(
    ! [B_306] :
      ( r2_hidden('#skF_6',B_306)
      | ~ r1_tarski(k1_setfam_1('#skF_7'),B_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2638,c_2055])).

tff(c_2680,plain,(
    ! [A_307] :
      ( r2_hidden('#skF_6',A_307)
      | ~ r2_hidden(A_307,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32,c_2658])).

tff(c_2692,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_2054,c_2680])).

tff(c_2707,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_2692])).

tff(c_2709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1972,c_2707])).

tff(c_2711,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2189])).

tff(c_2057,plain,(
    ! [B_252] :
      ( r2_hidden('#skF_8',B_252)
      | ~ r1_tarski('#skF_7',B_252) ) ),
    inference(resolution,[status(thm)],[c_1985,c_2041])).

tff(c_2064,plain,(
    ! [B_252] :
      ( ~ v1_xboole_0(B_252)
      | ~ r1_tarski('#skF_7',B_252) ) ),
    inference(resolution,[status(thm)],[c_2057,c_8])).

tff(c_2746,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2711,c_2064])).

tff(c_2754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_2746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.87  
% 4.67/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.87  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 4.67/1.87  
% 4.67/1.87  %Foreground sorts:
% 4.67/1.87  
% 4.67/1.87  
% 4.67/1.87  %Background operators:
% 4.67/1.87  
% 4.67/1.87  
% 4.67/1.87  %Foreground operators:
% 4.67/1.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.67/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.67/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.87  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 4.67/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.67/1.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.67/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.67/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.67/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.67/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.87  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.67/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.67/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.67/1.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.67/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.67/1.87  
% 4.67/1.90  tff(f_60, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.67/1.90  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.67/1.90  tff(f_46, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 4.67/1.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.67/1.90  tff(f_113, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 4.67/1.90  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.67/1.90  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 4.67/1.90  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 4.67/1.90  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 4.67/1.90  tff(f_101, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 4.67/1.90  tff(f_92, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.67/1.90  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.67/1.90  tff(f_86, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 4.67/1.90  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.67/1.90  tff(c_1990, plain, (![B_238, A_239]: (v1_xboole_0(B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(A_239)) | ~v1_xboole_0(A_239))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.90  tff(c_2005, plain, (![A_15]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_22, c_1990])).
% 4.67/1.90  tff(c_2006, plain, (![A_15]: (~v1_xboole_0(A_15))), inference(splitLeft, [status(thm)], [c_2005])).
% 4.67/1.90  tff(c_14, plain, (![A_10]: (v1_xboole_0('#skF_2'(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.67/1.90  tff(c_2009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2006, c_14])).
% 4.67/1.90  tff(c_2010, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_2005])).
% 4.67/1.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.90  tff(c_115, plain, (![A_56, B_57]: (~r2_hidden('#skF_1'(A_56, B_57), B_57) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.90  tff(c_120, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_115])).
% 4.67/1.90  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.67/1.90  tff(c_1512, plain, (![A_201, B_202]: (r2_hidden('#skF_3'(A_201, B_202), B_202) | k1_xboole_0=B_202 | ~m1_subset_1(B_202, k1_zfmisc_1(A_201)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.67/1.90  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.67/1.90  tff(c_1574, plain, (![B_205, A_206]: (~v1_xboole_0(B_205) | k1_xboole_0=B_205 | ~m1_subset_1(B_205, k1_zfmisc_1(A_206)))), inference(resolution, [status(thm)], [c_1512, c_8])).
% 4.67/1.90  tff(c_1603, plain, (~v1_xboole_0('#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_42, c_1574])).
% 4.67/1.90  tff(c_1627, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1603])).
% 4.67/1.90  tff(c_1377, plain, (![A_181, B_182]: (k6_setfam_1(A_181, B_182)=k1_setfam_1(B_182) | ~m1_subset_1(B_182, k1_zfmisc_1(k1_zfmisc_1(A_181))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.67/1.90  tff(c_1394, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_1377])).
% 4.67/1.90  tff(c_1718, plain, (![A_217, B_218]: (k8_setfam_1(A_217, B_218)=k6_setfam_1(A_217, B_218) | k1_xboole_0=B_218 | ~m1_subset_1(B_218, k1_zfmisc_1(k1_zfmisc_1(A_217))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.67/1.90  tff(c_1729, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_42, c_1718])).
% 4.67/1.90  tff(c_1737, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_1729])).
% 4.67/1.90  tff(c_1741, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1737])).
% 4.67/1.90  tff(c_82, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.90  tff(c_95, plain, (![A_15]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_22, c_82])).
% 4.67/1.90  tff(c_96, plain, (![A_15]: (~v1_xboole_0(A_15))), inference(splitLeft, [status(thm)], [c_95])).
% 4.67/1.90  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_14])).
% 4.67/1.90  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_95])).
% 4.67/1.90  tff(c_1758, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1741, c_101])).
% 4.67/1.90  tff(c_1762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1627, c_1758])).
% 4.67/1.90  tff(c_1763, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_1737])).
% 4.67/1.90  tff(c_44, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.67/1.90  tff(c_75, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.67/1.90  tff(c_1778, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1763, c_75])).
% 4.67/1.90  tff(c_1764, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_1737])).
% 4.67/1.90  tff(c_1544, plain, (![A_203, B_204]: (r2_hidden('#skF_4'(A_203, B_204), A_203) | r1_tarski(B_204, k1_setfam_1(A_203)) | k1_xboole_0=A_203)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.67/1.90  tff(c_50, plain, (![D_33]: (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.67/1.90  tff(c_132, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_50])).
% 4.67/1.90  tff(c_52, plain, (![D_33]: (r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.67/1.90  tff(c_121, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 4.67/1.90  tff(c_54, plain, (![D_33]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.67/1.90  tff(c_199, plain, (![D_68]: (r2_hidden('#skF_6', D_68) | ~r2_hidden(D_68, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_75, c_54])).
% 4.67/1.90  tff(c_204, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_121, c_199])).
% 4.67/1.90  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_204])).
% 4.67/1.90  tff(c_214, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 4.67/1.90  tff(c_218, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_214, c_8])).
% 4.67/1.90  tff(c_463, plain, (![A_95, B_96]: (r2_hidden('#skF_3'(A_95, B_96), B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.67/1.90  tff(c_213, plain, (![D_33]: (r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 4.67/1.90  tff(c_485, plain, (![A_95]: (r2_hidden('#skF_6', '#skF_3'(A_95, '#skF_7')) | k1_xboole_0='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_95)))), inference(resolution, [status(thm)], [c_463, c_213])).
% 4.67/1.90  tff(c_709, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_485])).
% 4.67/1.90  tff(c_234, plain, (![C_72, B_73, A_74]: (r2_hidden(C_72, B_73) | ~r2_hidden(C_72, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.90  tff(c_247, plain, (![B_73]: (r2_hidden('#skF_8', B_73) | ~r1_tarski('#skF_7', B_73))), inference(resolution, [status(thm)], [c_121, c_234])).
% 4.67/1.90  tff(c_392, plain, (![A_87, C_88, B_89]: (m1_subset_1(A_87, C_88) | ~m1_subset_1(B_89, k1_zfmisc_1(C_88)) | ~r2_hidden(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.67/1.90  tff(c_402, plain, (![A_90, A_91]: (m1_subset_1(A_90, A_91) | ~r2_hidden(A_90, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_392])).
% 4.67/1.90  tff(c_416, plain, (![A_91]: (m1_subset_1('#skF_8', A_91) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_247, c_402])).
% 4.67/1.90  tff(c_432, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_416])).
% 4.67/1.90  tff(c_718, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_709, c_432])).
% 4.67/1.90  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_718])).
% 4.67/1.90  tff(c_729, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_485])).
% 4.67/1.90  tff(c_338, plain, (![A_81, B_82]: (k6_setfam_1(A_81, B_82)=k1_setfam_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.67/1.90  tff(c_350, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_338])).
% 4.67/1.90  tff(c_959, plain, (![A_140, B_141]: (k8_setfam_1(A_140, B_141)=k6_setfam_1(A_140, B_141) | k1_xboole_0=B_141 | ~m1_subset_1(B_141, k1_zfmisc_1(k1_zfmisc_1(A_140))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.67/1.90  tff(c_970, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_42, c_959])).
% 4.67/1.90  tff(c_978, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_970])).
% 4.67/1.90  tff(c_979, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_729, c_978])).
% 4.67/1.90  tff(c_985, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_979, c_75])).
% 4.67/1.90  tff(c_825, plain, (![A_131, B_132]: (r2_hidden('#skF_4'(A_131, B_132), A_131) | r1_tarski(B_132, k1_setfam_1(A_131)) | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.67/1.90  tff(c_843, plain, (![B_132]: (r2_hidden('#skF_6', '#skF_4'('#skF_7', B_132)) | r1_tarski(B_132, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_825, c_213])).
% 4.67/1.90  tff(c_859, plain, (![B_132]: (r2_hidden('#skF_6', '#skF_4'('#skF_7', B_132)) | r1_tarski(B_132, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_729, c_843])).
% 4.67/1.90  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.67/1.90  tff(c_768, plain, (![B_121, A_122]: (~r1_tarski(B_121, '#skF_4'(A_122, B_121)) | r1_tarski(B_121, k1_setfam_1(A_122)) | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.67/1.90  tff(c_1148, plain, (![A_154, A_155]: (r1_tarski(k1_tarski(A_154), k1_setfam_1(A_155)) | k1_xboole_0=A_155 | ~r2_hidden(A_154, '#skF_4'(A_155, k1_tarski(A_154))))), inference(resolution, [status(thm)], [c_12, c_768])).
% 4.67/1.90  tff(c_1156, plain, (k1_xboole_0='#skF_7' | r1_tarski(k1_tarski('#skF_6'), k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_859, c_1148])).
% 4.67/1.90  tff(c_1172, plain, (r1_tarski(k1_tarski('#skF_6'), k1_setfam_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_729, c_1156])).
% 4.67/1.90  tff(c_10, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | ~r1_tarski(k1_tarski(A_8), B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.67/1.90  tff(c_1186, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_1172, c_10])).
% 4.67/1.90  tff(c_1198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_985, c_1186])).
% 4.67/1.90  tff(c_1201, plain, (![A_156]: (m1_subset_1('#skF_8', A_156))), inference(splitRight, [status(thm)], [c_416])).
% 4.67/1.90  tff(c_24, plain, (![B_18, A_16]: (v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_16)) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.90  tff(c_1212, plain, (![A_16]: (v1_xboole_0('#skF_8') | ~v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_1201, c_24])).
% 4.67/1.90  tff(c_1217, plain, (![A_16]: (~v1_xboole_0(A_16))), inference(negUnitSimplification, [status(thm)], [c_218, c_1212])).
% 4.67/1.90  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1217, c_101])).
% 4.67/1.90  tff(c_1222, plain, (![D_33]: (r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 4.67/1.90  tff(c_1572, plain, (![B_204]: (r2_hidden('#skF_6', '#skF_4'('#skF_7', B_204)) | r1_tarski(B_204, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_1544, c_1222])).
% 4.67/1.90  tff(c_1765, plain, (![B_204]: (r2_hidden('#skF_6', '#skF_4'('#skF_7', B_204)) | r1_tarski(B_204, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_1764, c_1572])).
% 4.67/1.90  tff(c_1499, plain, (![B_199, A_200]: (~r1_tarski(B_199, '#skF_4'(A_200, B_199)) | r1_tarski(B_199, k1_setfam_1(A_200)) | k1_xboole_0=A_200)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.67/1.90  tff(c_1879, plain, (![A_229, A_230]: (r1_tarski(k1_tarski(A_229), k1_setfam_1(A_230)) | k1_xboole_0=A_230 | ~r2_hidden(A_229, '#skF_4'(A_230, k1_tarski(A_229))))), inference(resolution, [status(thm)], [c_12, c_1499])).
% 4.67/1.90  tff(c_1883, plain, (k1_xboole_0='#skF_7' | r1_tarski(k1_tarski('#skF_6'), k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_1765, c_1879])).
% 4.67/1.90  tff(c_1894, plain, (r1_tarski(k1_tarski('#skF_6'), k1_setfam_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1764, c_1883])).
% 4.67/1.90  tff(c_1903, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_1894, c_10])).
% 4.67/1.90  tff(c_1911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1778, c_1903])).
% 4.67/1.90  tff(c_1912, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1603])).
% 4.67/1.90  tff(c_26, plain, (![A_19]: (k8_setfam_1(A_19, k1_xboole_0)=A_19 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.67/1.90  tff(c_56, plain, (![A_19]: (k8_setfam_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 4.67/1.90  tff(c_1927, plain, (![A_19]: (k8_setfam_1(A_19, '#skF_7')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_1912, c_56])).
% 4.67/1.90  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.67/1.90  tff(c_1248, plain, (![C_163, B_164, A_165]: (r2_hidden(C_163, B_164) | ~r2_hidden(C_163, A_165) | ~r1_tarski(A_165, B_164))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.90  tff(c_1262, plain, (![B_166]: (r2_hidden('#skF_6', B_166) | ~r1_tarski('#skF_5', B_166))), inference(resolution, [status(thm)], [c_40, c_1248])).
% 4.67/1.90  tff(c_1280, plain, (~r1_tarski('#skF_5', k8_setfam_1('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_1262, c_75])).
% 4.67/1.90  tff(c_1967, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1280])).
% 4.67/1.90  tff(c_1971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_1967])).
% 4.67/1.90  tff(c_1972, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 4.67/1.90  tff(c_2012, plain, (![A_242, B_243]: (r2_hidden('#skF_1'(A_242, B_243), A_242) | r1_tarski(A_242, B_243))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.90  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.90  tff(c_2020, plain, (![A_242]: (r1_tarski(A_242, A_242))), inference(resolution, [status(thm)], [c_2012, c_4])).
% 4.67/1.90  tff(c_1973, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_44])).
% 4.67/1.90  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.67/1.90  tff(c_1985, plain, (r2_hidden('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1973, c_46])).
% 4.67/1.90  tff(c_2041, plain, (![C_249, B_250, A_251]: (r2_hidden(C_249, B_250) | ~r2_hidden(C_249, A_251) | ~r1_tarski(A_251, B_250))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.90  tff(c_2054, plain, (![B_250]: (r2_hidden('#skF_8', B_250) | ~r1_tarski('#skF_7', B_250))), inference(resolution, [status(thm)], [c_1985, c_2041])).
% 4.67/1.90  tff(c_32, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.67/1.90  tff(c_2142, plain, (![A_261, B_262]: (k6_setfam_1(A_261, B_262)=k1_setfam_1(B_262) | ~m1_subset_1(B_262, k1_zfmisc_1(k1_zfmisc_1(A_261))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.67/1.90  tff(c_2154, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_2142])).
% 4.67/1.90  tff(c_2592, plain, (![A_304, B_305]: (k8_setfam_1(A_304, B_305)=k6_setfam_1(A_304, B_305) | k1_xboole_0=B_305 | ~m1_subset_1(B_305, k1_zfmisc_1(k1_zfmisc_1(A_304))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.67/1.90  tff(c_2603, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_42, c_2592])).
% 4.67/1.90  tff(c_2611, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_2603])).
% 4.67/1.90  tff(c_2615, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_2611])).
% 4.67/1.90  tff(c_2157, plain, (![A_263, C_264, B_265]: (m1_subset_1(A_263, C_264) | ~m1_subset_1(B_265, k1_zfmisc_1(C_264)) | ~r2_hidden(A_263, B_265))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.67/1.90  tff(c_2178, plain, (![A_267, A_268]: (m1_subset_1(A_267, A_268) | ~r2_hidden(A_267, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_2157])).
% 4.67/1.90  tff(c_2189, plain, (![A_268]: (m1_subset_1('#skF_8', A_268) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_2054, c_2178])).
% 4.67/1.90  tff(c_2204, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2189])).
% 4.67/1.90  tff(c_2628, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_2204])).
% 4.67/1.90  tff(c_2637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2020, c_2628])).
% 4.67/1.90  tff(c_2638, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_2611])).
% 4.67/1.90  tff(c_2055, plain, (![B_250]: (r2_hidden('#skF_6', B_250) | ~r1_tarski(k8_setfam_1('#skF_5', '#skF_7'), B_250))), inference(resolution, [status(thm)], [c_1973, c_2041])).
% 4.67/1.90  tff(c_2658, plain, (![B_306]: (r2_hidden('#skF_6', B_306) | ~r1_tarski(k1_setfam_1('#skF_7'), B_306))), inference(demodulation, [status(thm), theory('equality')], [c_2638, c_2055])).
% 4.67/1.90  tff(c_2680, plain, (![A_307]: (r2_hidden('#skF_6', A_307) | ~r2_hidden(A_307, '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_2658])).
% 4.67/1.90  tff(c_2692, plain, (r2_hidden('#skF_6', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_2054, c_2680])).
% 4.67/1.90  tff(c_2707, plain, (r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_2692])).
% 4.67/1.90  tff(c_2709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1972, c_2707])).
% 4.67/1.90  tff(c_2711, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2189])).
% 4.67/1.90  tff(c_2057, plain, (![B_252]: (r2_hidden('#skF_8', B_252) | ~r1_tarski('#skF_7', B_252))), inference(resolution, [status(thm)], [c_1985, c_2041])).
% 4.67/1.90  tff(c_2064, plain, (![B_252]: (~v1_xboole_0(B_252) | ~r1_tarski('#skF_7', B_252))), inference(resolution, [status(thm)], [c_2057, c_8])).
% 4.67/1.90  tff(c_2746, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2711, c_2064])).
% 4.67/1.90  tff(c_2754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2010, c_2746])).
% 4.67/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.90  
% 4.67/1.90  Inference rules
% 4.67/1.90  ----------------------
% 4.67/1.90  #Ref     : 0
% 4.67/1.90  #Sup     : 566
% 4.67/1.90  #Fact    : 0
% 4.67/1.90  #Define  : 0
% 4.67/1.90  #Split   : 38
% 4.67/1.90  #Chain   : 0
% 4.67/1.90  #Close   : 0
% 4.67/1.90  
% 4.67/1.90  Ordering : KBO
% 4.67/1.90  
% 4.67/1.90  Simplification rules
% 4.67/1.90  ----------------------
% 4.67/1.90  #Subsume      : 222
% 4.67/1.90  #Demod        : 173
% 4.67/1.90  #Tautology    : 82
% 4.67/1.90  #SimpNegUnit  : 44
% 4.67/1.90  #BackRed      : 105
% 4.67/1.90  
% 4.67/1.90  #Partial instantiations: 0
% 4.67/1.90  #Strategies tried      : 1
% 4.67/1.90  
% 4.67/1.90  Timing (in seconds)
% 4.67/1.90  ----------------------
% 4.67/1.90  Preprocessing        : 0.34
% 4.67/1.90  Parsing              : 0.17
% 4.67/1.90  CNF conversion       : 0.02
% 4.67/1.90  Main loop            : 0.75
% 4.67/1.90  Inferencing          : 0.27
% 4.67/1.90  Reduction            : 0.22
% 4.67/1.90  Demodulation         : 0.14
% 4.67/1.90  BG Simplification    : 0.03
% 4.67/1.90  Subsumption          : 0.15
% 4.67/1.90  Abstraction          : 0.03
% 4.67/1.90  MUC search           : 0.00
% 4.67/1.90  Cooper               : 0.00
% 4.67/1.90  Total                : 1.15
% 4.67/1.90  Index Insertion      : 0.00
% 4.67/1.90  Index Deletion       : 0.00
% 4.67/1.90  Index Matching       : 0.00
% 4.67/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
