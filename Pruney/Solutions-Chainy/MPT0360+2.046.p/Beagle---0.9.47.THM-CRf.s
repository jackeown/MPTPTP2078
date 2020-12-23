%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:24 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 169 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 363 expanded)
%              Number of equality atoms :   19 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_64,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_73,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_143,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_436,plain,(
    ! [B_89,B_90,A_91] :
      ( r2_hidden(B_89,B_90)
      | ~ r1_tarski(A_91,B_90)
      | ~ m1_subset_1(B_89,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_18,c_143])).

tff(c_471,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,'#skF_4')
      | ~ m1_subset_1(B_89,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_436])).

tff(c_515,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_26,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_19] : m1_subset_1(k2_subset_1(A_19),k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_56,plain,(
    ! [A_19] : m1_subset_1(A_19,k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_110,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_1'(A_41,B_42),A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [A_41,B_42] :
      ( ~ v1_xboole_0(A_41)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_110,c_12])).

tff(c_24,plain,(
    ! [A_16] : k1_subset_1(A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [A_26,B_27] :
      ( k1_subset_1(A_26) = B_27
      | ~ r1_tarski(B_27,k3_subset_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_202,plain,(
    ! [B_63,A_64] :
      ( k1_xboole_0 = B_63
      | ~ r1_tarski(B_63,k3_subset_1(A_64,B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42])).

tff(c_263,plain,(
    ! [A_68,A_69] :
      ( k1_xboole_0 = A_68
      | ~ m1_subset_1(A_68,k1_zfmisc_1(A_69))
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_114,c_202])).

tff(c_279,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_56,c_263])).

tff(c_519,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_515,c_279])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_519])).

tff(c_525,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(B_49,A_50)
      | ~ r2_hidden(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1('#skF_1'(A_1,B_2),A_1)
      | v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_18] : m1_subset_1(k1_subset_1(A_18),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_34,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = k2_subset_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [A_26] :
      ( r1_tarski(k1_subset_1(A_26),k3_subset_1(A_26,k1_subset_1(A_26)))
      | ~ m1_subset_1(k1_subset_1(A_26),k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_51,plain,(
    ! [A_26] :
      ( r1_tarski(k1_subset_1(A_26),k2_subset_1(A_26))
      | ~ m1_subset_1(k1_subset_1(A_26),k1_zfmisc_1(A_26)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_53,plain,(
    ! [A_26] : r1_tarski(k1_subset_1(A_26),k2_subset_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_51])).

tff(c_54,plain,(
    ! [A_26] : r1_tarski(k1_subset_1(A_26),A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_53])).

tff(c_59,plain,(
    ! [A_26] : r1_tarski(k1_xboole_0,A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_54])).

tff(c_55,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_60,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_55])).

tff(c_307,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(k3_subset_1(A_74,C_75),k3_subset_1(A_74,B_76))
      | ~ r1_tarski(B_76,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_323,plain,(
    ! [A_21,C_75] :
      ( r1_tarski(k3_subset_1(A_21,C_75),A_21)
      | ~ r1_tarski(k1_xboole_0,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_307])).

tff(c_331,plain,(
    ! [A_21,C_75] :
      ( r1_tarski(k3_subset_1(A_21,C_75),A_21)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_59,c_323])).

tff(c_46,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_469,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,k3_subset_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_89,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_436])).

tff(c_728,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k3_subset_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_109,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_469])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_965,plain,(
    ! [B_122,B_123] :
      ( r2_hidden(B_122,B_123)
      | ~ r1_tarski(k3_subset_1('#skF_2','#skF_4'),B_123)
      | ~ m1_subset_1(B_122,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_728,c_2])).

tff(c_971,plain,(
    ! [B_122] :
      ( r2_hidden(B_122,'#skF_2')
      | ~ m1_subset_1(B_122,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_331,c_965])).

tff(c_994,plain,(
    ! [B_124] :
      ( r2_hidden(B_124,'#skF_2')
      | ~ m1_subset_1(B_124,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_971])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1029,plain,(
    ! [A_126] :
      ( r1_tarski(A_126,'#skF_2')
      | ~ m1_subset_1('#skF_1'(A_126,'#skF_2'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_994,c_4])).

tff(c_1033,plain,
    ( v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_1029])).

tff(c_1039,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_1033])).

tff(c_32,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_zfmisc_1(A_12),k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_452,plain,(
    ! [B_89,B_13,A_12] :
      ( r2_hidden(B_89,k1_zfmisc_1(B_13))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_436])).

tff(c_1661,plain,(
    ! [B_156,B_157,A_158] :
      ( r2_hidden(B_156,k1_zfmisc_1(B_157))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_158))
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_452])).

tff(c_1696,plain,(
    ! [A_160,B_161] :
      ( r2_hidden(A_160,k1_zfmisc_1(B_161))
      | ~ r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_56,c_1661])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ r2_hidden(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1705,plain,(
    ! [A_160,B_161] :
      ( m1_subset_1(A_160,k1_zfmisc_1(B_161))
      | v1_xboole_0(k1_zfmisc_1(B_161))
      | ~ r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_1696,c_16])).

tff(c_1713,plain,(
    ! [A_160,B_161] :
      ( m1_subset_1(A_160,k1_zfmisc_1(B_161))
      | ~ r1_tarski(A_160,B_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1705])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1471,plain,(
    ! [A_148,A_149,B_150,C_151] :
      ( r1_tarski(A_148,k3_subset_1(A_149,B_150))
      | ~ r1_tarski(A_148,k3_subset_1(A_149,C_151))
      | ~ r1_tarski(B_150,C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_307,c_8])).

tff(c_1494,plain,(
    ! [B_150] :
      ( r1_tarski('#skF_3',k3_subset_1('#skF_2',B_150))
      | ~ r1_tarski(B_150,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_150,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46,c_1471])).

tff(c_2125,plain,(
    ! [B_178] :
      ( r1_tarski('#skF_3',k3_subset_1('#skF_2',B_178))
      | ~ r1_tarski(B_178,'#skF_4')
      | ~ m1_subset_1(B_178,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1494])).

tff(c_57,plain,(
    ! [B_27,A_26] :
      ( k1_xboole_0 = B_27
      | ~ r1_tarski(B_27,k3_subset_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42])).

tff(c_2141,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2125,c_57])).

tff(c_2160,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2141])).

tff(c_2161,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2160])).

tff(c_2167,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1713,c_2161])).

tff(c_2174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_2167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:10:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.66  
% 3.73/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.67  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.73/1.67  
% 3.73/1.67  %Foreground sorts:
% 3.73/1.67  
% 3.73/1.67  
% 3.73/1.67  %Background operators:
% 3.73/1.67  
% 3.73/1.67  
% 3.73/1.67  %Foreground operators:
% 3.73/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.73/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.67  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.73/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.73/1.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.73/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.67  
% 3.99/1.68  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.99/1.68  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.99/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.99/1.68  tff(f_66, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.99/1.68  tff(f_70, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.99/1.68  tff(f_45, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 3.99/1.68  tff(f_64, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.99/1.68  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.99/1.68  tff(f_68, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 3.99/1.68  tff(f_75, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.99/1.68  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.99/1.68  tff(f_73, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.99/1.68  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.99/1.68  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.99/1.68  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.99/1.68  tff(c_48, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.99/1.68  tff(c_18, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.68  tff(c_143, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.68  tff(c_436, plain, (![B_89, B_90, A_91]: (r2_hidden(B_89, B_90) | ~r1_tarski(A_91, B_90) | ~m1_subset_1(B_89, A_91) | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_18, c_143])).
% 3.99/1.68  tff(c_471, plain, (![B_89]: (r2_hidden(B_89, '#skF_4') | ~m1_subset_1(B_89, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_436])).
% 3.99/1.68  tff(c_515, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_471])).
% 3.99/1.68  tff(c_26, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.99/1.68  tff(c_30, plain, (![A_19]: (m1_subset_1(k2_subset_1(A_19), k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.99/1.68  tff(c_56, plain, (![A_19]: (m1_subset_1(A_19, k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.99/1.68  tff(c_110, plain, (![A_41, B_42]: (r2_hidden('#skF_1'(A_41, B_42), A_41) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.68  tff(c_12, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.99/1.68  tff(c_114, plain, (![A_41, B_42]: (~v1_xboole_0(A_41) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_110, c_12])).
% 3.99/1.68  tff(c_24, plain, (![A_16]: (k1_subset_1(A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.99/1.68  tff(c_42, plain, (![A_26, B_27]: (k1_subset_1(A_26)=B_27 | ~r1_tarski(B_27, k3_subset_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.99/1.68  tff(c_202, plain, (![B_63, A_64]: (k1_xboole_0=B_63 | ~r1_tarski(B_63, k3_subset_1(A_64, B_63)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42])).
% 3.99/1.68  tff(c_263, plain, (![A_68, A_69]: (k1_xboole_0=A_68 | ~m1_subset_1(A_68, k1_zfmisc_1(A_69)) | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_114, c_202])).
% 3.99/1.68  tff(c_279, plain, (![A_19]: (k1_xboole_0=A_19 | ~v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_56, c_263])).
% 3.99/1.68  tff(c_519, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_515, c_279])).
% 3.99/1.68  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_519])).
% 3.99/1.68  tff(c_525, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_471])).
% 3.99/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.68  tff(c_122, plain, (![B_49, A_50]: (m1_subset_1(B_49, A_50) | ~r2_hidden(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.68  tff(c_130, plain, (![A_1, B_2]: (m1_subset_1('#skF_1'(A_1, B_2), A_1) | v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_122])).
% 3.99/1.68  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.99/1.68  tff(c_28, plain, (![A_18]: (m1_subset_1(k1_subset_1(A_18), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.99/1.68  tff(c_58, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 3.99/1.68  tff(c_34, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=k2_subset_1(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.99/1.68  tff(c_40, plain, (![A_26]: (r1_tarski(k1_subset_1(A_26), k3_subset_1(A_26, k1_subset_1(A_26))) | ~m1_subset_1(k1_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.99/1.68  tff(c_51, plain, (![A_26]: (r1_tarski(k1_subset_1(A_26), k2_subset_1(A_26)) | ~m1_subset_1(k1_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_40])).
% 3.99/1.68  tff(c_53, plain, (![A_26]: (r1_tarski(k1_subset_1(A_26), k2_subset_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_51])).
% 3.99/1.68  tff(c_54, plain, (![A_26]: (r1_tarski(k1_subset_1(A_26), A_26))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_53])).
% 3.99/1.68  tff(c_59, plain, (![A_26]: (r1_tarski(k1_xboole_0, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_54])).
% 3.99/1.68  tff(c_55, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34])).
% 3.99/1.68  tff(c_60, plain, (![A_21]: (k3_subset_1(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_55])).
% 3.99/1.68  tff(c_307, plain, (![A_74, C_75, B_76]: (r1_tarski(k3_subset_1(A_74, C_75), k3_subset_1(A_74, B_76)) | ~r1_tarski(B_76, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.99/1.68  tff(c_323, plain, (![A_21, C_75]: (r1_tarski(k3_subset_1(A_21, C_75), A_21) | ~r1_tarski(k1_xboole_0, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_21)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_307])).
% 3.99/1.68  tff(c_331, plain, (![A_21, C_75]: (r1_tarski(k3_subset_1(A_21, C_75), A_21) | ~m1_subset_1(C_75, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_59, c_323])).
% 3.99/1.68  tff(c_46, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.99/1.68  tff(c_469, plain, (![B_89]: (r2_hidden(B_89, k3_subset_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_89, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_436])).
% 3.99/1.68  tff(c_728, plain, (![B_109]: (r2_hidden(B_109, k3_subset_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_109, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_525, c_469])).
% 3.99/1.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.68  tff(c_965, plain, (![B_122, B_123]: (r2_hidden(B_122, B_123) | ~r1_tarski(k3_subset_1('#skF_2', '#skF_4'), B_123) | ~m1_subset_1(B_122, '#skF_3'))), inference(resolution, [status(thm)], [c_728, c_2])).
% 3.99/1.68  tff(c_971, plain, (![B_122]: (r2_hidden(B_122, '#skF_2') | ~m1_subset_1(B_122, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_331, c_965])).
% 3.99/1.68  tff(c_994, plain, (![B_124]: (r2_hidden(B_124, '#skF_2') | ~m1_subset_1(B_124, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_971])).
% 3.99/1.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.68  tff(c_1029, plain, (![A_126]: (r1_tarski(A_126, '#skF_2') | ~m1_subset_1('#skF_1'(A_126, '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_994, c_4])).
% 3.99/1.68  tff(c_1033, plain, (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_130, c_1029])).
% 3.99/1.68  tff(c_1039, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_525, c_1033])).
% 3.99/1.68  tff(c_32, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.99/1.68  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k1_zfmisc_1(A_12), k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.99/1.68  tff(c_452, plain, (![B_89, B_13, A_12]: (r2_hidden(B_89, k1_zfmisc_1(B_13)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_14, c_436])).
% 3.99/1.68  tff(c_1661, plain, (![B_156, B_157, A_158]: (r2_hidden(B_156, k1_zfmisc_1(B_157)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_158)) | ~r1_tarski(A_158, B_157))), inference(negUnitSimplification, [status(thm)], [c_32, c_452])).
% 3.99/1.68  tff(c_1696, plain, (![A_160, B_161]: (r2_hidden(A_160, k1_zfmisc_1(B_161)) | ~r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_56, c_1661])).
% 3.99/1.68  tff(c_16, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~r2_hidden(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.99/1.68  tff(c_1705, plain, (![A_160, B_161]: (m1_subset_1(A_160, k1_zfmisc_1(B_161)) | v1_xboole_0(k1_zfmisc_1(B_161)) | ~r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_1696, c_16])).
% 3.99/1.68  tff(c_1713, plain, (![A_160, B_161]: (m1_subset_1(A_160, k1_zfmisc_1(B_161)) | ~r1_tarski(A_160, B_161))), inference(negUnitSimplification, [status(thm)], [c_32, c_1705])).
% 3.99/1.68  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.99/1.68  tff(c_1471, plain, (![A_148, A_149, B_150, C_151]: (r1_tarski(A_148, k3_subset_1(A_149, B_150)) | ~r1_tarski(A_148, k3_subset_1(A_149, C_151)) | ~r1_tarski(B_150, C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(A_149)) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)))), inference(resolution, [status(thm)], [c_307, c_8])).
% 3.99/1.68  tff(c_1494, plain, (![B_150]: (r1_tarski('#skF_3', k3_subset_1('#skF_2', B_150)) | ~r1_tarski(B_150, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_150, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_46, c_1471])).
% 3.99/1.68  tff(c_2125, plain, (![B_178]: (r1_tarski('#skF_3', k3_subset_1('#skF_2', B_178)) | ~r1_tarski(B_178, '#skF_4') | ~m1_subset_1(B_178, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1494])).
% 3.99/1.68  tff(c_57, plain, (![B_27, A_26]: (k1_xboole_0=B_27 | ~r1_tarski(B_27, k3_subset_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42])).
% 3.99/1.68  tff(c_2141, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_2125, c_57])).
% 3.99/1.68  tff(c_2160, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2141])).
% 3.99/1.68  tff(c_2161, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_2160])).
% 3.99/1.68  tff(c_2167, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1713, c_2161])).
% 3.99/1.68  tff(c_2174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1039, c_2167])).
% 3.99/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.68  
% 3.99/1.68  Inference rules
% 3.99/1.68  ----------------------
% 3.99/1.68  #Ref     : 0
% 3.99/1.68  #Sup     : 468
% 3.99/1.68  #Fact    : 0
% 3.99/1.68  #Define  : 0
% 3.99/1.68  #Split   : 13
% 3.99/1.68  #Chain   : 0
% 3.99/1.68  #Close   : 0
% 3.99/1.68  
% 3.99/1.69  Ordering : KBO
% 3.99/1.69  
% 3.99/1.69  Simplification rules
% 3.99/1.69  ----------------------
% 3.99/1.69  #Subsume      : 165
% 3.99/1.69  #Demod        : 131
% 3.99/1.69  #Tautology    : 104
% 3.99/1.69  #SimpNegUnit  : 58
% 3.99/1.69  #BackRed      : 0
% 3.99/1.69  
% 3.99/1.69  #Partial instantiations: 0
% 3.99/1.69  #Strategies tried      : 1
% 3.99/1.69  
% 3.99/1.69  Timing (in seconds)
% 3.99/1.69  ----------------------
% 3.99/1.69  Preprocessing        : 0.31
% 3.99/1.69  Parsing              : 0.16
% 3.99/1.69  CNF conversion       : 0.02
% 3.99/1.69  Main loop            : 0.59
% 3.99/1.69  Inferencing          : 0.19
% 3.99/1.69  Reduction            : 0.18
% 3.99/1.69  Demodulation         : 0.12
% 3.99/1.69  BG Simplification    : 0.02
% 3.99/1.69  Subsumption          : 0.15
% 3.99/1.69  Abstraction          : 0.02
% 3.99/1.69  MUC search           : 0.00
% 3.99/1.69  Cooper               : 0.00
% 3.99/1.69  Total                : 0.94
% 3.99/1.69  Index Insertion      : 0.00
% 3.99/1.69  Index Deletion       : 0.00
% 3.99/1.69  Index Matching       : 0.00
% 3.99/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
