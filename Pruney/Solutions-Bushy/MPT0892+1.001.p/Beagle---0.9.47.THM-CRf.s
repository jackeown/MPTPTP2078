%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0892+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:01 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 ( 122 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ~ r1_xboole_0(k3_zfmisc_1(A,B,C),k3_zfmisc_1(D,E,F))
       => ( ~ r1_xboole_0(A,D)
          & ~ r1_xboole_0(B,E)
          & ~ r1_xboole_0(C,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_mcart_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_10,plain,
    ( r1_xboole_0('#skF_3','#skF_6')
    | r1_xboole_0('#skF_2','#skF_5')
    | r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( r1_xboole_0(B_5,A_4)
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_17,plain,(
    r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_4])).

tff(c_37,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( ~ r1_xboole_0(A_15,B_16)
      | r1_xboole_0(k2_zfmisc_1(A_15,C_17),k2_zfmisc_1(B_16,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ! [B_16,D_18,A_15,C_17] :
      ( r1_xboole_0(k2_zfmisc_1(B_16,D_18),k2_zfmisc_1(A_15,C_17))
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_37,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_170,plain,(
    ! [A_76,B_73,C_74,C_72,A_75] :
      ( ~ r1_xboole_0(A_76,k2_zfmisc_1(A_75,B_73))
      | r1_xboole_0(k2_zfmisc_1(A_76,C_72),k3_zfmisc_1(A_75,B_73,C_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_37])).

tff(c_203,plain,(
    ! [C_89,B_87,A_88,A_92,C_91,B_90] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_92,B_90),k2_zfmisc_1(A_88,B_87))
      | r1_xboole_0(k3_zfmisc_1(A_92,B_90,C_91),k3_zfmisc_1(A_88,B_87,C_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_170])).

tff(c_12,plain,(
    ~ r1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_215,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_203,c_12])).

tff(c_224,plain,(
    ~ r1_xboole_0('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_215])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_224])).

tff(c_236,plain,
    ( r1_xboole_0('#skF_2','#skF_5')
    | r1_xboole_0('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_238,plain,(
    r1_xboole_0('#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_271,plain,(
    ! [C_100,D_101,A_102,B_103] :
      ( ~ r1_xboole_0(C_100,D_101)
      | r1_xboole_0(k2_zfmisc_1(A_102,C_100),k2_zfmisc_1(B_103,D_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_301,plain,(
    ! [C_115,A_116,B_113,C_112,A_114] :
      ( ~ r1_xboole_0(C_112,C_115)
      | r1_xboole_0(k2_zfmisc_1(A_114,C_112),k3_zfmisc_1(A_116,B_113,C_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_271])).

tff(c_355,plain,(
    ! [B_137,A_136,B_141,C_139,C_138,A_140] :
      ( ~ r1_xboole_0(C_139,C_138)
      | r1_xboole_0(k3_zfmisc_1(A_140,B_137,C_139),k3_zfmisc_1(A_136,B_141,C_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_301])).

tff(c_358,plain,(
    ~ r1_xboole_0('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_355,c_12])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_358])).

tff(c_371,plain,(
    r1_xboole_0('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_375,plain,(
    r1_xboole_0('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_371,c_4])).

tff(c_395,plain,(
    ! [C_145,D_146,A_147,B_148] :
      ( ~ r1_xboole_0(C_145,D_146)
      | r1_xboole_0(k2_zfmisc_1(A_147,C_145),k2_zfmisc_1(B_148,D_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_404,plain,(
    ! [B_148,D_146,A_147,C_145] :
      ( r1_xboole_0(k2_zfmisc_1(B_148,D_146),k2_zfmisc_1(A_147,C_145))
      | ~ r1_xboole_0(C_145,D_146) ) ),
    inference(resolution,[status(thm)],[c_395,c_4])).

tff(c_405,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( ~ r1_xboole_0(A_149,B_150)
      | r1_xboole_0(k2_zfmisc_1(A_149,C_151),k2_zfmisc_1(B_150,D_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_517,plain,(
    ! [C_200,B_199,C_197,A_198,A_201] :
      ( ~ r1_xboole_0(A_198,k2_zfmisc_1(A_201,B_199))
      | r1_xboole_0(k2_zfmisc_1(A_198,C_197),k3_zfmisc_1(A_201,B_199,C_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_405])).

tff(c_561,plain,(
    ! [B_219,C_221,A_217,C_220,A_222,B_218] :
      ( ~ r1_xboole_0(k2_zfmisc_1(A_222,B_219),k2_zfmisc_1(A_217,B_218))
      | r1_xboole_0(k3_zfmisc_1(A_222,B_219,C_220),k3_zfmisc_1(A_217,B_218,C_221)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_517])).

tff(c_573,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_561,c_12])).

tff(c_582,plain,(
    ~ r1_xboole_0('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_404,c_573])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_582])).

%------------------------------------------------------------------------------
