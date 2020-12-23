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
% DateTime   : Thu Dec  3 09:58:01 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 382 expanded)
%              Number of leaves         :   31 ( 136 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 ( 727 expanded)
%              Number of equality atoms :   58 ( 202 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2217,plain,(
    ! [A_231,B_232] :
      ( ~ r2_hidden('#skF_1'(A_231,B_232),B_232)
      | r1_tarski(A_231,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2222,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_2217])).

tff(c_16,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_62,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_58])).

tff(c_119,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    ! [C_49] :
      ( ~ r1_xboole_0('#skF_5','#skF_6')
      | ~ r2_hidden(C_49,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_119])).

tff(c_137,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_1174,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_2'(A_147,B_148),k3_xboole_0(A_147,B_148))
      | r1_xboole_0(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1197,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_5')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1174])).

tff(c_1202,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_1197])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1388,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_2'('#skF_5','#skF_6'),B_161)
      | ~ r1_tarski('#skF_5',B_161) ) ),
    inference(resolution,[status(thm)],[c_1202,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_140,plain,(
    k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_142,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_140])).

tff(c_36,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k1_setfam_1(B_30),k1_setfam_1(A_29))
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_68])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,(
    k3_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_79,c_18])).

tff(c_122,plain,(
    ! [C_49] :
      ( ~ r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_119])).

tff(c_169,plain,(
    ~ r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_172,plain,(
    k3_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_169])).

tff(c_174,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_172])).

tff(c_348,plain,(
    ! [A_71,B_72] :
      ( k6_setfam_1(A_71,B_72) = k1_setfam_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_365,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_348])).

tff(c_796,plain,(
    ! [A_105,B_106] :
      ( k8_setfam_1(A_105,B_106) = k6_setfam_1(A_105,B_106)
      | k1_xboole_0 = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_818,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_796])).

tff(c_832,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_818])).

tff(c_833,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_832])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_364,plain,(
    k6_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_348])).

tff(c_815,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k6_setfam_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_796])).

tff(c_829,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_815])).

tff(c_830,plain,(
    k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_829])).

tff(c_38,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_837,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_38])).

tff(c_857,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_837])).

tff(c_860,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_857])).

tff(c_866,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_860])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_866])).

tff(c_869,plain,(
    ! [C_49] : ~ r2_hidden(C_49,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_1406,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1388,c_869])).

tff(c_1421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1406])).

tff(c_1430,plain,(
    ! [C_164] : ~ r2_hidden(C_164,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_1440,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16,c_1430])).

tff(c_2343,plain,(
    ! [A_247] :
      ( r2_hidden('#skF_3'(A_247),A_247)
      | A_247 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_16])).

tff(c_1551,plain,(
    ! [A_181,B_182] :
      ( r1_xboole_0(A_181,B_182)
      | k3_xboole_0(A_181,B_182) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_10])).

tff(c_1452,plain,(
    ~ r1_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_1560,plain,(
    k3_xboole_0('#skF_6',k1_zfmisc_1('#skF_4')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_1551,c_1452])).

tff(c_1565,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1560])).

tff(c_1634,plain,(
    ! [A_193,B_194] :
      ( k6_setfam_1(A_193,B_194) = k1_setfam_1(B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k1_zfmisc_1(A_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1648,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_1634])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k8_setfam_1(A_18,B_19) = k6_setfam_1(A_18,B_19)
      | k1_xboole_0 = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2143,plain,(
    ! [A_228,B_229] :
      ( k8_setfam_1(A_228,B_229) = k6_setfam_1(A_228,B_229)
      | B_229 = '#skF_5'
      | ~ m1_subset_1(B_229,k1_zfmisc_1(k1_zfmisc_1(A_228))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_24])).

tff(c_2166,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_2143])).

tff(c_2176,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1648,c_2166])).

tff(c_2177,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1565,c_2176])).

tff(c_20,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_18] :
      ( k8_setfam_1(A_18,k1_xboole_0) = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [A_18] : k8_setfam_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_1446,plain,(
    ! [A_18] : k8_setfam_1(A_18,'#skF_5') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1440,c_46])).

tff(c_1468,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_38])).

tff(c_2183,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2177,c_1468])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k8_setfam_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2187,plain,
    ( m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2177,c_26])).

tff(c_2191,plain,(
    m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2187])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2201,plain,(
    r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2191,c_30])).

tff(c_2206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2183,c_2201])).

tff(c_2207,plain,(
    ! [C_49] : ~ r2_hidden(C_49,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_2359,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2343,c_2207])).

tff(c_2365,plain,(
    ! [A_18] : k8_setfam_1(A_18,'#skF_6') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2359,c_1446])).

tff(c_2281,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_38])).

tff(c_2388,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2365,c_2281])).

tff(c_2391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2222,c_2388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:53:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.67  
% 3.95/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.95/1.67  
% 3.95/1.67  %Foreground sorts:
% 3.95/1.67  
% 3.95/1.67  
% 3.95/1.67  %Background operators:
% 3.95/1.67  
% 3.95/1.67  
% 3.95/1.67  %Foreground operators:
% 3.95/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.67  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.95/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.95/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.95/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.67  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.95/1.67  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.95/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.95/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.95/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.95/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.95/1.67  
% 4.04/1.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.04/1.69  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.04/1.69  tff(f_109, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 4.04/1.69  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.04/1.69  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.04/1.69  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.04/1.69  tff(f_99, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 4.04/1.69  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.04/1.69  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 4.04/1.69  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 4.04/1.69  tff(f_64, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.04/1.69  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 4.04/1.69  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.69  tff(c_2217, plain, (![A_231, B_232]: (~r2_hidden('#skF_1'(A_231, B_232), B_232) | r1_tarski(A_231, B_232))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.69  tff(c_2222, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_2217])).
% 4.04/1.69  tff(c_16, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.04/1.69  tff(c_40, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.04/1.69  tff(c_58, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.04/1.69  tff(c_62, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_40, c_58])).
% 4.04/1.69  tff(c_119, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.04/1.69  tff(c_131, plain, (![C_49]: (~r1_xboole_0('#skF_5', '#skF_6') | ~r2_hidden(C_49, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_119])).
% 4.04/1.69  tff(c_137, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_131])).
% 4.04/1.69  tff(c_1174, plain, (![A_147, B_148]: (r2_hidden('#skF_2'(A_147, B_148), k3_xboole_0(A_147, B_148)) | r1_xboole_0(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.04/1.69  tff(c_1197, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), '#skF_5') | r1_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_62, c_1174])).
% 4.04/1.69  tff(c_1202, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_137, c_1197])).
% 4.04/1.69  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.69  tff(c_1388, plain, (![B_161]: (r2_hidden('#skF_2'('#skF_5', '#skF_6'), B_161) | ~r1_tarski('#skF_5', B_161))), inference(resolution, [status(thm)], [c_1202, c_2])).
% 4.04/1.69  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.04/1.69  tff(c_140, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_137])).
% 4.04/1.69  tff(c_142, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_140])).
% 4.04/1.69  tff(c_36, plain, (![B_30, A_29]: (r1_tarski(k1_setfam_1(B_30), k1_setfam_1(A_29)) | k1_xboole_0=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.04/1.69  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.04/1.69  tff(c_68, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.69  tff(c_79, plain, (r1_tarski('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_68])).
% 4.04/1.69  tff(c_18, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.04/1.69  tff(c_93, plain, (k3_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_79, c_18])).
% 4.04/1.69  tff(c_122, plain, (![C_49]: (~r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4')) | ~r2_hidden(C_49, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_119])).
% 4.04/1.69  tff(c_169, plain, (~r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_122])).
% 4.04/1.69  tff(c_172, plain, (k3_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_169])).
% 4.04/1.69  tff(c_174, plain, (k1_xboole_0!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_172])).
% 4.04/1.69  tff(c_348, plain, (![A_71, B_72]: (k6_setfam_1(A_71, B_72)=k1_setfam_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/1.69  tff(c_365, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_348])).
% 4.04/1.69  tff(c_796, plain, (![A_105, B_106]: (k8_setfam_1(A_105, B_106)=k6_setfam_1(A_105, B_106) | k1_xboole_0=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_105))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.69  tff(c_818, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_42, c_796])).
% 4.04/1.69  tff(c_832, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_818])).
% 4.04/1.69  tff(c_833, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_174, c_832])).
% 4.04/1.69  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.04/1.69  tff(c_364, plain, (k6_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_348])).
% 4.04/1.69  tff(c_815, plain, (k8_setfam_1('#skF_4', '#skF_5')=k6_setfam_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_44, c_796])).
% 4.04/1.69  tff(c_829, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_364, c_815])).
% 4.04/1.69  tff(c_830, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_142, c_829])).
% 4.04/1.69  tff(c_38, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.04/1.69  tff(c_837, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_38])).
% 4.04/1.69  tff(c_857, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_837])).
% 4.04/1.69  tff(c_860, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_857])).
% 4.04/1.69  tff(c_866, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_860])).
% 4.04/1.69  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_866])).
% 4.04/1.69  tff(c_869, plain, (![C_49]: (~r2_hidden(C_49, '#skF_6'))), inference(splitRight, [status(thm)], [c_122])).
% 4.04/1.69  tff(c_1406, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1388, c_869])).
% 4.04/1.69  tff(c_1421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1406])).
% 4.04/1.69  tff(c_1430, plain, (![C_164]: (~r2_hidden(C_164, '#skF_5'))), inference(splitRight, [status(thm)], [c_131])).
% 4.04/1.69  tff(c_1440, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_16, c_1430])).
% 4.04/1.69  tff(c_2343, plain, (![A_247]: (r2_hidden('#skF_3'(A_247), A_247) | A_247='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_16])).
% 4.04/1.69  tff(c_1551, plain, (![A_181, B_182]: (r1_xboole_0(A_181, B_182) | k3_xboole_0(A_181, B_182)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_10])).
% 4.04/1.69  tff(c_1452, plain, (~r1_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_122])).
% 4.04/1.69  tff(c_1560, plain, (k3_xboole_0('#skF_6', k1_zfmisc_1('#skF_4'))!='#skF_5'), inference(resolution, [status(thm)], [c_1551, c_1452])).
% 4.04/1.69  tff(c_1565, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1560])).
% 4.04/1.69  tff(c_1634, plain, (![A_193, B_194]: (k6_setfam_1(A_193, B_194)=k1_setfam_1(B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(k1_zfmisc_1(A_193))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.04/1.69  tff(c_1648, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_1634])).
% 4.04/1.69  tff(c_24, plain, (![A_18, B_19]: (k8_setfam_1(A_18, B_19)=k6_setfam_1(A_18, B_19) | k1_xboole_0=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.69  tff(c_2143, plain, (![A_228, B_229]: (k8_setfam_1(A_228, B_229)=k6_setfam_1(A_228, B_229) | B_229='#skF_5' | ~m1_subset_1(B_229, k1_zfmisc_1(k1_zfmisc_1(A_228))))), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_24])).
% 4.04/1.69  tff(c_2166, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42, c_2143])).
% 4.04/1.69  tff(c_2176, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1648, c_2166])).
% 4.04/1.69  tff(c_2177, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1565, c_2176])).
% 4.04/1.69  tff(c_20, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.04/1.69  tff(c_22, plain, (![A_18]: (k8_setfam_1(A_18, k1_xboole_0)=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.04/1.69  tff(c_46, plain, (![A_18]: (k8_setfam_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 4.04/1.69  tff(c_1446, plain, (![A_18]: (k8_setfam_1(A_18, '#skF_5')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_1440, c_46])).
% 4.04/1.69  tff(c_1468, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_38])).
% 4.04/1.69  tff(c_2183, plain, (~r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2177, c_1468])).
% 4.04/1.69  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(k8_setfam_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.04/1.69  tff(c_2187, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2177, c_26])).
% 4.04/1.69  tff(c_2191, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2187])).
% 4.04/1.69  tff(c_30, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.04/1.69  tff(c_2201, plain, (r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_2191, c_30])).
% 4.04/1.69  tff(c_2206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2183, c_2201])).
% 4.04/1.69  tff(c_2207, plain, (![C_49]: (~r2_hidden(C_49, '#skF_6'))), inference(splitRight, [status(thm)], [c_122])).
% 4.04/1.69  tff(c_2359, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2343, c_2207])).
% 4.04/1.69  tff(c_2365, plain, (![A_18]: (k8_setfam_1(A_18, '#skF_6')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_2359, c_1446])).
% 4.04/1.69  tff(c_2281, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_38])).
% 4.04/1.69  tff(c_2388, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2365, c_2281])).
% 4.04/1.69  tff(c_2391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2222, c_2388])).
% 4.04/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  Inference rules
% 4.04/1.69  ----------------------
% 4.04/1.69  #Ref     : 0
% 4.04/1.69  #Sup     : 534
% 4.04/1.69  #Fact    : 0
% 4.04/1.69  #Define  : 0
% 4.04/1.69  #Split   : 12
% 4.04/1.69  #Chain   : 0
% 4.04/1.69  #Close   : 0
% 4.04/1.69  
% 4.04/1.69  Ordering : KBO
% 4.04/1.69  
% 4.04/1.69  Simplification rules
% 4.04/1.69  ----------------------
% 4.04/1.69  #Subsume      : 82
% 4.04/1.69  #Demod        : 142
% 4.04/1.69  #Tautology    : 186
% 4.04/1.69  #SimpNegUnit  : 21
% 4.04/1.69  #BackRed      : 33
% 4.04/1.69  
% 4.04/1.69  #Partial instantiations: 0
% 4.04/1.69  #Strategies tried      : 1
% 4.04/1.69  
% 4.04/1.69  Timing (in seconds)
% 4.04/1.69  ----------------------
% 4.04/1.69  Preprocessing        : 0.32
% 4.04/1.69  Parsing              : 0.17
% 4.04/1.69  CNF conversion       : 0.02
% 4.04/1.69  Main loop            : 0.57
% 4.04/1.69  Inferencing          : 0.21
% 4.04/1.69  Reduction            : 0.18
% 4.04/1.69  Demodulation         : 0.12
% 4.04/1.69  BG Simplification    : 0.02
% 4.04/1.70  Subsumption          : 0.10
% 4.04/1.70  Abstraction          : 0.03
% 4.04/1.70  MUC search           : 0.00
% 4.04/1.70  Cooper               : 0.00
% 4.04/1.70  Total                : 0.93
% 4.04/1.70  Index Insertion      : 0.00
% 4.04/1.70  Index Deletion       : 0.00
% 4.04/1.70  Index Matching       : 0.00
% 4.04/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
