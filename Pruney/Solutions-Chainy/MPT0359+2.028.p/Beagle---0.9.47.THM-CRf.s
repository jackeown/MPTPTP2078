%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:12 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 235 expanded)
%              Number of leaves         :   42 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 382 expanded)
%              Number of equality atoms :   50 ( 127 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_101,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_94,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_107,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_94,plain,(
    ! [A_45] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_88,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_315,plain,(
    ! [B_88,A_89] :
      ( r2_hidden(B_88,A_89)
      | ~ m1_subset_1(B_88,A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    ! [C_34,A_30] :
      ( r1_tarski(C_34,A_30)
      | ~ r2_hidden(C_34,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_342,plain,(
    ! [B_88,A_30] :
      ( r1_tarski(B_88,A_30)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_315,c_62])).

tff(c_389,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(B_92,A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_342])).

tff(c_407,plain,(
    ! [A_45] : r1_tarski(k1_xboole_0,A_45) ),
    inference(resolution,[status(thm)],[c_94,c_389])).

tff(c_82,plain,(
    ! [A_37] : k1_subset_1(A_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_84,plain,(
    ! [A_38] : k2_subset_1(A_38) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_92,plain,(
    ! [A_44] : k3_subset_1(A_44,k1_subset_1(A_44)) = k2_subset_1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_106,plain,(
    ! [A_44] : k3_subset_1(A_44,k1_subset_1(A_44)) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_92])).

tff(c_108,plain,(
    ! [A_44] : k3_subset_1(A_44,k1_xboole_0) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_106])).

tff(c_578,plain,(
    ! [A_104,B_105] :
      ( k3_subset_1(A_104,k3_subset_1(A_104,B_105)) = B_105
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_587,plain,(
    ! [A_45] : k3_subset_1(A_45,k3_subset_1(A_45,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_578])).

tff(c_592,plain,(
    ! [A_45] : k3_subset_1(A_45,A_45) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_587])).

tff(c_98,plain,
    ( k2_subset_1('#skF_10') != '#skF_11'
    | ~ r1_tarski(k3_subset_1('#skF_10','#skF_11'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_105,plain,
    ( '#skF_11' != '#skF_10'
    | ~ r1_tarski(k3_subset_1('#skF_10','#skF_11'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_98])).

tff(c_187,plain,(
    ~ r1_tarski(k3_subset_1('#skF_10','#skF_11'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_104,plain,
    ( r1_tarski(k3_subset_1('#skF_10','#skF_11'),'#skF_11')
    | k2_subset_1('#skF_10') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_107,plain,
    ( r1_tarski(k3_subset_1('#skF_10','#skF_11'),'#skF_11')
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_104])).

tff(c_196,plain,(
    '#skF_11' = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_107])).

tff(c_197,plain,(
    ~ r1_tarski(k3_subset_1('#skF_10','#skF_10'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_187])).

tff(c_593,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_197])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_593])).

tff(c_597,plain,(
    '#skF_11' != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1177,plain,(
    ! [A_164,B_165] :
      ( k4_xboole_0(A_164,B_165) = k3_subset_1(A_164,B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1193,plain,(
    k4_xboole_0('#skF_10','#skF_11') = k3_subset_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_96,c_1177])).

tff(c_1535,plain,(
    ! [D_191,A_192,B_193] :
      ( r2_hidden(D_191,k4_xboole_0(A_192,B_193))
      | r2_hidden(D_191,B_193)
      | ~ r2_hidden(D_191,A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1623,plain,(
    ! [D_201] :
      ( r2_hidden(D_201,k3_subset_1('#skF_10','#skF_11'))
      | r2_hidden(D_201,'#skF_11')
      | ~ r2_hidden(D_201,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_1535])).

tff(c_598,plain,(
    r1_tarski(k3_subset_1('#skF_10','#skF_11'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_621,plain,(
    ! [A_114,B_115] :
      ( k3_xboole_0(A_114,B_115) = A_114
      | ~ r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_625,plain,(
    k3_xboole_0(k3_subset_1('#skF_10','#skF_11'),'#skF_11') = k3_subset_1('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_598,c_621])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_666,plain,(
    ! [D_13] :
      ( r2_hidden(D_13,'#skF_11')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_12])).

tff(c_1650,plain,(
    ! [D_202] :
      ( r2_hidden(D_202,'#skF_11')
      | ~ r2_hidden(D_202,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1623,c_666])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1668,plain,(
    ! [A_203] :
      ( r1_tarski(A_203,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_203,'#skF_11'),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1650,c_6])).

tff(c_1683,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_8,c_1668])).

tff(c_1271,plain,(
    ! [A_173,B_174] :
      ( k3_subset_1(A_173,k3_subset_1(A_173,B_174)) = B_174
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1280,plain,(
    ! [A_45] : k3_subset_1(A_45,k3_subset_1(A_45,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_1271])).

tff(c_1285,plain,(
    ! [A_45] : k3_subset_1(A_45,A_45) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1280])).

tff(c_737,plain,(
    ! [A_133,B_134] :
      ( ~ r2_hidden('#skF_1'(A_133,B_134),B_134)
      | r1_tarski(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_751,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_737])).

tff(c_64,plain,(
    ! [C_34,A_30] :
      ( r2_hidden(C_34,k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_636,plain,(
    ! [B_119,A_120] :
      ( m1_subset_1(B_119,A_120)
      | ~ r2_hidden(B_119,A_120)
      | v1_xboole_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_639,plain,(
    ! [C_34,A_30] :
      ( m1_subset_1(C_34,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(resolution,[status(thm)],[c_64,c_636])).

tff(c_642,plain,(
    ! [C_34,A_30] :
      ( m1_subset_1(C_34,k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_639])).

tff(c_1327,plain,(
    ! [A_178,C_179] :
      ( k4_xboole_0(A_178,C_179) = k3_subset_1(A_178,C_179)
      | ~ r1_tarski(C_179,A_178) ) ),
    inference(resolution,[status(thm)],[c_642,c_1177])).

tff(c_1330,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_subset_1(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_751,c_1327])).

tff(c_1341,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_1330])).

tff(c_46,plain,(
    ! [A_20] : k3_xboole_0(A_20,A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_869,plain,(
    ! [A_138,B_139] : k5_xboole_0(A_138,k3_xboole_0(A_138,B_139)) = k4_xboole_0(A_138,B_139) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_899,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k4_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_869])).

tff(c_1348,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_899])).

tff(c_688,plain,(
    ! [B_128,A_129] :
      ( r2_hidden(B_128,A_129)
      | ~ m1_subset_1(B_128,A_129)
      | v1_xboole_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_703,plain,(
    ! [B_128,A_30] :
      ( r1_tarski(B_128,A_30)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_688,c_62])).

tff(c_710,plain,(
    ! [B_130,A_131] :
      ( r1_tarski(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_703])).

tff(c_726,plain,(
    r1_tarski('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_96,c_710])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_731,plain,(
    k3_xboole_0('#skF_11','#skF_10') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_726,c_58])).

tff(c_887,plain,(
    k5_xboole_0('#skF_11','#skF_11') = k4_xboole_0('#skF_11','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_869])).

tff(c_1428,plain,(
    k4_xboole_0('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_887])).

tff(c_1191,plain,(
    ! [A_30,C_34] :
      ( k4_xboole_0(A_30,C_34) = k3_subset_1(A_30,C_34)
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(resolution,[status(thm)],[c_642,c_1177])).

tff(c_1686,plain,(
    k4_xboole_0('#skF_11','#skF_10') = k3_subset_1('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_1683,c_1191])).

tff(c_1691,plain,(
    k3_subset_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_1686])).

tff(c_1281,plain,(
    ! [A_30,C_34] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,C_34)) = C_34
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(resolution,[status(thm)],[c_642,c_1271])).

tff(c_1696,plain,
    ( k3_subset_1('#skF_11',k1_xboole_0) = '#skF_10'
    | ~ r1_tarski('#skF_10','#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_1691,c_1281])).

tff(c_1700,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1683,c_108,c_1696])).

tff(c_1702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_1700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.64  
% 3.60/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.64  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9
% 3.60/1.64  
% 3.60/1.64  %Foreground sorts:
% 3.60/1.64  
% 3.60/1.64  
% 3.60/1.64  %Background operators:
% 3.60/1.64  
% 3.60/1.64  
% 3.60/1.64  %Foreground operators:
% 3.60/1.64  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.60/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.64  tff('#skF_11', type, '#skF_11': $i).
% 3.60/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.60/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.60/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.60/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.64  tff('#skF_10', type, '#skF_10': $i).
% 3.60/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.60/1.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.60/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.60/1.64  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.60/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.60/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.64  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.60/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.60/1.64  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.60/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.60/1.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.60/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.64  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.60/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.64  
% 3.60/1.66  tff(f_109, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.60/1.66  tff(f_101, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.60/1.66  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.60/1.66  tff(f_77, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.60/1.66  tff(f_92, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.60/1.66  tff(f_94, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.60/1.66  tff(f_107, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.60/1.66  tff(f_105, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.60/1.66  tff(f_116, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 3.60/1.66  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.60/1.66  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.60/1.66  tff(f_53, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.60/1.66  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.60/1.66  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.60/1.66  tff(f_55, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.60/1.66  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.60/1.66  tff(c_94, plain, (![A_45]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.66  tff(c_88, plain, (![A_41]: (~v1_xboole_0(k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.60/1.66  tff(c_315, plain, (![B_88, A_89]: (r2_hidden(B_88, A_89) | ~m1_subset_1(B_88, A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.66  tff(c_62, plain, (![C_34, A_30]: (r1_tarski(C_34, A_30) | ~r2_hidden(C_34, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.60/1.66  tff(c_342, plain, (![B_88, A_30]: (r1_tarski(B_88, A_30) | ~m1_subset_1(B_88, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_315, c_62])).
% 3.60/1.66  tff(c_389, plain, (![B_92, A_93]: (r1_tarski(B_92, A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)))), inference(negUnitSimplification, [status(thm)], [c_88, c_342])).
% 3.60/1.66  tff(c_407, plain, (![A_45]: (r1_tarski(k1_xboole_0, A_45))), inference(resolution, [status(thm)], [c_94, c_389])).
% 3.60/1.66  tff(c_82, plain, (![A_37]: (k1_subset_1(A_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.60/1.66  tff(c_84, plain, (![A_38]: (k2_subset_1(A_38)=A_38)), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.60/1.66  tff(c_92, plain, (![A_44]: (k3_subset_1(A_44, k1_subset_1(A_44))=k2_subset_1(A_44))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.60/1.66  tff(c_106, plain, (![A_44]: (k3_subset_1(A_44, k1_subset_1(A_44))=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_92])).
% 3.60/1.66  tff(c_108, plain, (![A_44]: (k3_subset_1(A_44, k1_xboole_0)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_106])).
% 3.60/1.66  tff(c_578, plain, (![A_104, B_105]: (k3_subset_1(A_104, k3_subset_1(A_104, B_105))=B_105 | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/1.66  tff(c_587, plain, (![A_45]: (k3_subset_1(A_45, k3_subset_1(A_45, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_578])).
% 3.60/1.66  tff(c_592, plain, (![A_45]: (k3_subset_1(A_45, A_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_587])).
% 3.60/1.66  tff(c_98, plain, (k2_subset_1('#skF_10')!='#skF_11' | ~r1_tarski(k3_subset_1('#skF_10', '#skF_11'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.60/1.66  tff(c_105, plain, ('#skF_11'!='#skF_10' | ~r1_tarski(k3_subset_1('#skF_10', '#skF_11'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_98])).
% 3.60/1.66  tff(c_187, plain, (~r1_tarski(k3_subset_1('#skF_10', '#skF_11'), '#skF_11')), inference(splitLeft, [status(thm)], [c_105])).
% 3.60/1.66  tff(c_104, plain, (r1_tarski(k3_subset_1('#skF_10', '#skF_11'), '#skF_11') | k2_subset_1('#skF_10')='#skF_11'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.60/1.66  tff(c_107, plain, (r1_tarski(k3_subset_1('#skF_10', '#skF_11'), '#skF_11') | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_104])).
% 3.60/1.66  tff(c_196, plain, ('#skF_11'='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_187, c_107])).
% 3.60/1.66  tff(c_197, plain, (~r1_tarski(k3_subset_1('#skF_10', '#skF_10'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_187])).
% 3.60/1.66  tff(c_593, plain, (~r1_tarski(k1_xboole_0, '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_592, c_197])).
% 3.60/1.66  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_407, c_593])).
% 3.60/1.66  tff(c_597, plain, ('#skF_11'!='#skF_10'), inference(splitRight, [status(thm)], [c_105])).
% 3.60/1.66  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.60/1.66  tff(c_96, plain, (m1_subset_1('#skF_11', k1_zfmisc_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.60/1.66  tff(c_1177, plain, (![A_164, B_165]: (k4_xboole_0(A_164, B_165)=k3_subset_1(A_164, B_165) | ~m1_subset_1(B_165, k1_zfmisc_1(A_164)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.60/1.66  tff(c_1193, plain, (k4_xboole_0('#skF_10', '#skF_11')=k3_subset_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_96, c_1177])).
% 3.60/1.66  tff(c_1535, plain, (![D_191, A_192, B_193]: (r2_hidden(D_191, k4_xboole_0(A_192, B_193)) | r2_hidden(D_191, B_193) | ~r2_hidden(D_191, A_192))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.60/1.66  tff(c_1623, plain, (![D_201]: (r2_hidden(D_201, k3_subset_1('#skF_10', '#skF_11')) | r2_hidden(D_201, '#skF_11') | ~r2_hidden(D_201, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1193, c_1535])).
% 3.60/1.66  tff(c_598, plain, (r1_tarski(k3_subset_1('#skF_10', '#skF_11'), '#skF_11')), inference(splitRight, [status(thm)], [c_105])).
% 3.60/1.66  tff(c_621, plain, (![A_114, B_115]: (k3_xboole_0(A_114, B_115)=A_114 | ~r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.60/1.66  tff(c_625, plain, (k3_xboole_0(k3_subset_1('#skF_10', '#skF_11'), '#skF_11')=k3_subset_1('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_598, c_621])).
% 3.60/1.66  tff(c_12, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.60/1.66  tff(c_666, plain, (![D_13]: (r2_hidden(D_13, '#skF_11') | ~r2_hidden(D_13, k3_subset_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_625, c_12])).
% 3.60/1.66  tff(c_1650, plain, (![D_202]: (r2_hidden(D_202, '#skF_11') | ~r2_hidden(D_202, '#skF_10'))), inference(resolution, [status(thm)], [c_1623, c_666])).
% 3.60/1.66  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.60/1.66  tff(c_1668, plain, (![A_203]: (r1_tarski(A_203, '#skF_11') | ~r2_hidden('#skF_1'(A_203, '#skF_11'), '#skF_10'))), inference(resolution, [status(thm)], [c_1650, c_6])).
% 3.60/1.66  tff(c_1683, plain, (r1_tarski('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_8, c_1668])).
% 3.60/1.66  tff(c_1271, plain, (![A_173, B_174]: (k3_subset_1(A_173, k3_subset_1(A_173, B_174))=B_174 | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/1.66  tff(c_1280, plain, (![A_45]: (k3_subset_1(A_45, k3_subset_1(A_45, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_1271])).
% 3.60/1.66  tff(c_1285, plain, (![A_45]: (k3_subset_1(A_45, A_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1280])).
% 3.60/1.66  tff(c_737, plain, (![A_133, B_134]: (~r2_hidden('#skF_1'(A_133, B_134), B_134) | r1_tarski(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.60/1.66  tff(c_751, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_737])).
% 3.60/1.66  tff(c_64, plain, (![C_34, A_30]: (r2_hidden(C_34, k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.60/1.66  tff(c_636, plain, (![B_119, A_120]: (m1_subset_1(B_119, A_120) | ~r2_hidden(B_119, A_120) | v1_xboole_0(A_120))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.66  tff(c_639, plain, (![C_34, A_30]: (m1_subset_1(C_34, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(resolution, [status(thm)], [c_64, c_636])).
% 3.60/1.66  tff(c_642, plain, (![C_34, A_30]: (m1_subset_1(C_34, k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(negUnitSimplification, [status(thm)], [c_88, c_639])).
% 3.60/1.66  tff(c_1327, plain, (![A_178, C_179]: (k4_xboole_0(A_178, C_179)=k3_subset_1(A_178, C_179) | ~r1_tarski(C_179, A_178))), inference(resolution, [status(thm)], [c_642, c_1177])).
% 3.60/1.66  tff(c_1330, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_subset_1(A_3, A_3))), inference(resolution, [status(thm)], [c_751, c_1327])).
% 3.60/1.66  tff(c_1341, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_1330])).
% 3.60/1.66  tff(c_46, plain, (![A_20]: (k3_xboole_0(A_20, A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.66  tff(c_869, plain, (![A_138, B_139]: (k5_xboole_0(A_138, k3_xboole_0(A_138, B_139))=k4_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.60/1.66  tff(c_899, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k4_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_46, c_869])).
% 3.60/1.66  tff(c_1348, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_899])).
% 3.60/1.66  tff(c_688, plain, (![B_128, A_129]: (r2_hidden(B_128, A_129) | ~m1_subset_1(B_128, A_129) | v1_xboole_0(A_129))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.66  tff(c_703, plain, (![B_128, A_30]: (r1_tarski(B_128, A_30) | ~m1_subset_1(B_128, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_688, c_62])).
% 3.60/1.66  tff(c_710, plain, (![B_130, A_131]: (r1_tarski(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)))), inference(negUnitSimplification, [status(thm)], [c_88, c_703])).
% 3.60/1.66  tff(c_726, plain, (r1_tarski('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_96, c_710])).
% 3.60/1.66  tff(c_58, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.60/1.66  tff(c_731, plain, (k3_xboole_0('#skF_11', '#skF_10')='#skF_11'), inference(resolution, [status(thm)], [c_726, c_58])).
% 3.60/1.66  tff(c_887, plain, (k5_xboole_0('#skF_11', '#skF_11')=k4_xboole_0('#skF_11', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_731, c_869])).
% 3.60/1.66  tff(c_1428, plain, (k4_xboole_0('#skF_11', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_887])).
% 3.60/1.66  tff(c_1191, plain, (![A_30, C_34]: (k4_xboole_0(A_30, C_34)=k3_subset_1(A_30, C_34) | ~r1_tarski(C_34, A_30))), inference(resolution, [status(thm)], [c_642, c_1177])).
% 3.60/1.66  tff(c_1686, plain, (k4_xboole_0('#skF_11', '#skF_10')=k3_subset_1('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_1683, c_1191])).
% 3.60/1.66  tff(c_1691, plain, (k3_subset_1('#skF_11', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_1686])).
% 3.60/1.66  tff(c_1281, plain, (![A_30, C_34]: (k3_subset_1(A_30, k3_subset_1(A_30, C_34))=C_34 | ~r1_tarski(C_34, A_30))), inference(resolution, [status(thm)], [c_642, c_1271])).
% 3.60/1.66  tff(c_1696, plain, (k3_subset_1('#skF_11', k1_xboole_0)='#skF_10' | ~r1_tarski('#skF_10', '#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1691, c_1281])).
% 3.60/1.66  tff(c_1700, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1683, c_108, c_1696])).
% 3.60/1.66  tff(c_1702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_597, c_1700])).
% 3.60/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.66  
% 3.60/1.66  Inference rules
% 3.60/1.66  ----------------------
% 3.60/1.66  #Ref     : 0
% 3.60/1.66  #Sup     : 380
% 3.60/1.66  #Fact    : 0
% 3.60/1.66  #Define  : 0
% 3.60/1.66  #Split   : 5
% 3.60/1.66  #Chain   : 0
% 3.60/1.66  #Close   : 0
% 3.60/1.66  
% 3.60/1.66  Ordering : KBO
% 3.60/1.66  
% 3.60/1.66  Simplification rules
% 3.60/1.66  ----------------------
% 3.60/1.66  #Subsume      : 41
% 3.60/1.66  #Demod        : 92
% 3.60/1.66  #Tautology    : 209
% 3.60/1.66  #SimpNegUnit  : 13
% 3.60/1.66  #BackRed      : 8
% 3.60/1.66  
% 3.60/1.66  #Partial instantiations: 0
% 3.60/1.66  #Strategies tried      : 1
% 3.60/1.66  
% 3.60/1.66  Timing (in seconds)
% 3.60/1.66  ----------------------
% 3.60/1.67  Preprocessing        : 0.40
% 3.60/1.67  Parsing              : 0.19
% 3.60/1.67  CNF conversion       : 0.03
% 3.60/1.67  Main loop            : 0.46
% 3.60/1.67  Inferencing          : 0.15
% 3.60/1.67  Reduction            : 0.15
% 3.60/1.67  Demodulation         : 0.11
% 3.60/1.67  BG Simplification    : 0.03
% 3.60/1.67  Subsumption          : 0.08
% 3.60/1.67  Abstraction          : 0.02
% 3.60/1.67  MUC search           : 0.00
% 3.60/1.67  Cooper               : 0.00
% 3.60/1.67  Total                : 0.90
% 3.60/1.67  Index Insertion      : 0.00
% 3.60/1.67  Index Deletion       : 0.00
% 3.60/1.67  Index Matching       : 0.00
% 3.60/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
