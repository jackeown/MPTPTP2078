%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:07 EST 2020

% Result     : Theorem 13.67s
% Output     : CNFRefutation 13.80s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 256 expanded)
%              Number of leaves         :   43 ( 102 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 435 expanded)
%              Number of equality atoms :   44 ( 149 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_94,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_104,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).

tff(f_64,axiom,(
    ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ! [D] :
              ( m1_subset_1(D,A)
             => ( A != k1_xboole_0
               => m1_subset_1(k1_enumset1(B,C,D),k1_zfmisc_1(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_subset_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_110,plain,(
    ! [A_71,B_72] : r1_xboole_0(k4_xboole_0(A_71,B_72),k4_xboole_0(B_72,A_71)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_4] :
      ( ~ r1_xboole_0(A_4,A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_115,plain,(
    ! [B_72] : k4_xboole_0(B_72,B_72) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_10])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_183,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( ~ r1_xboole_0(A_99,B_100)
      | r1_xboole_0(k2_zfmisc_1(A_99,C_101),k2_zfmisc_1(B_100,D_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_190,plain,(
    ! [B_106,D_107] :
      ( k2_zfmisc_1(B_106,D_107) = k1_xboole_0
      | ~ r1_xboole_0(B_106,B_106) ) ),
    inference(resolution,[status(thm)],[c_183,c_10])).

tff(c_199,plain,(
    ! [B_6,D_107] : k2_zfmisc_1(k4_xboole_0(B_6,B_6),D_107) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_190])).

tff(c_205,plain,(
    ! [D_107] : k2_zfmisc_1(k1_xboole_0,D_107) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_199])).

tff(c_207,plain,(
    ! [D_108] : k2_zfmisc_1(k1_xboole_0,D_108) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_199])).

tff(c_40,plain,(
    ! [C_36,A_34,B_35] :
      ( r1_tarski(k2_zfmisc_1(C_36,A_34),k2_zfmisc_1(C_36,B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_212,plain,(
    ! [B_35,D_108] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,B_35))
      | ~ r1_tarski(D_108,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_40])).

tff(c_231,plain,(
    ! [D_108,B_35] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(D_108,B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_212])).

tff(c_235,plain,(
    ! [D_108,B_35] : ~ r1_tarski(D_108,B_35) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_56,plain,(
    ! [A_45] : v1_xboole_0(k1_subset_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_80,plain,(
    ! [B_64,A_65] :
      ( ~ v1_xboole_0(B_64)
      | B_64 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_66] :
      ( o_0_0_xboole_0 = A_66
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_94,plain,(
    ! [A_45] : k1_subset_1(A_45) = o_0_0_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_87])).

tff(c_54,plain,(
    ! [A_44] : m1_subset_1(k1_subset_1(A_44),k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,(
    ! [A_46] :
      ( r1_tarski(k1_subset_1(A_46),k3_subset_1(A_46,k1_subset_1(A_46)))
      | ~ m1_subset_1(k1_subset_1(A_46),k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_70,plain,(
    ! [A_46] : r1_tarski(k1_subset_1(A_46),k3_subset_1(A_46,k1_subset_1(A_46))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58])).

tff(c_134,plain,(
    ! [A_46] : r1_tarski(o_0_0_xboole_0,k3_subset_1(A_46,o_0_0_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_70])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_134])).

tff(c_243,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_163,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(A_87,B_88)
      | ~ r1_tarski(A_87,k4_xboole_0(B_88,C_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,(
    ! [A_87,B_72] :
      ( r1_tarski(A_87,B_72)
      | ~ r1_tarski(A_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_163])).

tff(c_256,plain,(
    ! [B_72] : r1_tarski(k1_xboole_0,B_72) ),
    inference(resolution,[status(thm)],[c_243,c_166])).

tff(c_116,plain,(
    ! [B_73] : k4_xboole_0(B_73,B_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_10])).

tff(c_50,plain,(
    ! [C_43,B_42] : ~ r2_hidden(C_43,k4_xboole_0(B_42,k1_tarski(C_43))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_127,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_50])).

tff(c_889,plain,(
    ! [A_192,B_193] :
      ( r1_tarski('#skF_1'(A_192,B_193),A_192)
      | r2_hidden('#skF_2'(A_192,B_193),B_193)
      | k1_zfmisc_1(A_192) = B_193 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_925,plain,(
    ! [A_194] :
      ( r1_tarski('#skF_1'(A_194,k1_xboole_0),A_194)
      | k1_zfmisc_1(A_194) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_889,c_127])).

tff(c_152,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_xboole_0(A_81,C_82)
      | ~ r1_tarski(A_81,k4_xboole_0(B_83,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_156,plain,(
    ! [A_84,B_85] :
      ( r1_xboole_0(A_84,B_85)
      | ~ r1_tarski(A_84,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_152])).

tff(c_161,plain,(
    ! [B_85] :
      ( k1_xboole_0 = B_85
      | ~ r1_tarski(B_85,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_156,c_10])).

tff(c_951,plain,
    ( '#skF_1'(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_925,c_161])).

tff(c_953,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_30,plain,(
    ! [C_33,A_29] :
      ( r2_hidden(C_33,k1_zfmisc_1(A_29))
      | ~ r1_tarski(C_33,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_962,plain,(
    ! [C_33] :
      ( r2_hidden(C_33,k1_xboole_0)
      | ~ r1_tarski(C_33,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_30])).

tff(c_969,plain,(
    ! [C_195] : ~ r1_tarski(C_195,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_962])).

tff(c_982,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_256,c_969])).

tff(c_984,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_62,plain,(
    ! [A_48] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1040,plain,(
    ! [E_206,B_209,D_208,F_207,C_205,A_204] : k6_enumset1(A_204,A_204,A_204,B_209,C_205,D_208,E_206,F_207) = k4_enumset1(A_204,B_209,C_205,D_208,E_206,F_207) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] : k6_enumset1(A_26,A_26,A_26,A_26,A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1564,plain,(
    ! [D_234,E_235,F_236] : k4_enumset1(D_234,D_234,D_234,D_234,E_235,F_236) = k1_enumset1(D_234,E_235,F_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_26])).

tff(c_24,plain,(
    ! [A_25] : k4_enumset1(A_25,A_25,A_25,A_25,A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1580,plain,(
    ! [F_237] : k1_enumset1(F_237,F_237,F_237) = k1_tarski(F_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_1564,c_24])).

tff(c_64,plain,(
    ! [B_50,C_54,D_56,A_49] :
      ( m1_subset_1(k1_enumset1(B_50,C_54,D_56),k1_zfmisc_1(A_49))
      | k1_xboole_0 = A_49
      | ~ m1_subset_1(D_56,A_49)
      | ~ m1_subset_1(C_54,A_49)
      | ~ m1_subset_1(B_50,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52362,plain,(
    ! [F_1155,A_1156] :
      ( m1_subset_1(k1_tarski(F_1155),k1_zfmisc_1(A_1156))
      | k1_xboole_0 = A_1156
      | ~ m1_subset_1(F_1155,A_1156)
      | ~ m1_subset_1(F_1155,A_1156)
      | ~ m1_subset_1(F_1155,A_1156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_64])).

tff(c_68,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52367,plain,
    ( k1_zfmisc_1('#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52362,c_68])).

tff(c_52371,plain,(
    k1_zfmisc_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52367])).

tff(c_28,plain,(
    ! [C_33,A_29] :
      ( r1_tarski(C_33,A_29)
      | ~ r2_hidden(C_33,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2146,plain,(
    ! [A_280,A_281] :
      ( r1_tarski('#skF_2'(A_280,k1_zfmisc_1(A_281)),A_281)
      | r1_tarski('#skF_1'(A_280,k1_zfmisc_1(A_281)),A_280)
      | k1_zfmisc_1(A_281) = k1_zfmisc_1(A_280) ) ),
    inference(resolution,[status(thm)],[c_889,c_28])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27414,plain,(
    ! [A_766,B_767,C_768] :
      ( r1_tarski('#skF_2'(A_766,k1_zfmisc_1(k4_xboole_0(B_767,C_768))),B_767)
      | r1_tarski('#skF_1'(A_766,k1_zfmisc_1(k4_xboole_0(B_767,C_768))),A_766)
      | k1_zfmisc_1(k4_xboole_0(B_767,C_768)) = k1_zfmisc_1(A_766) ) ),
    inference(resolution,[status(thm)],[c_2146,c_6])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( r1_tarski('#skF_1'(A_29,B_30),A_29)
      | ~ r1_tarski('#skF_2'(A_29,B_30),A_29)
      | k1_zfmisc_1(A_29) = B_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_29119,plain,(
    ! [B_780,C_781] :
      ( r1_tarski('#skF_1'(B_780,k1_zfmisc_1(k4_xboole_0(B_780,C_781))),B_780)
      | k1_zfmisc_1(k4_xboole_0(B_780,C_781)) = k1_zfmisc_1(B_780) ) ),
    inference(resolution,[status(thm)],[c_27414,c_34])).

tff(c_29167,plain,(
    ! [B_72] :
      ( r1_tarski('#skF_1'(B_72,k1_zfmisc_1(k1_xboole_0)),B_72)
      | k1_zfmisc_1(k4_xboole_0(B_72,B_72)) = k1_zfmisc_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_29119])).

tff(c_29182,plain,(
    ! [B_72] :
      ( r1_tarski('#skF_1'(B_72,k1_zfmisc_1(k1_xboole_0)),B_72)
      | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_29167])).

tff(c_52426,plain,(
    ! [C_33] :
      ( r2_hidden(C_33,k1_xboole_0)
      | ~ r1_tarski(C_33,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52371,c_30])).

tff(c_52449,plain,(
    ! [C_1157] : ~ r1_tarski(C_1157,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_52426])).

tff(c_52511,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_29182,c_52449])).

tff(c_52600,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52371,c_52511])).

tff(c_52602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_984,c_52600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.67/6.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.80/6.39  
% 13.80/6.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.80/6.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 13.80/6.39  
% 13.80/6.39  %Foreground sorts:
% 13.80/6.39  
% 13.80/6.39  
% 13.80/6.39  %Background operators:
% 13.80/6.39  
% 13.80/6.39  
% 13.80/6.39  %Foreground operators:
% 13.80/6.39  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 13.80/6.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.80/6.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.80/6.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.80/6.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.80/6.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.80/6.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.80/6.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.80/6.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.80/6.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.80/6.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.80/6.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.80/6.39  tff('#skF_3', type, '#skF_3': $i).
% 13.80/6.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.80/6.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.80/6.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.80/6.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.80/6.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.80/6.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.80/6.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.80/6.39  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 13.80/6.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.80/6.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.80/6.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.80/6.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.80/6.39  
% 13.80/6.40  tff(f_46, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 13.80/6.40  tff(f_44, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 13.80/6.40  tff(f_85, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 13.80/6.40  tff(f_79, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 13.80/6.40  tff(f_96, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 13.80/6.40  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 13.80/6.41  tff(f_54, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 13.80/6.41  tff(f_94, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 13.80/6.41  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 13.80/6.41  tff(f_32, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.80/6.41  tff(f_92, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 13.80/6.41  tff(f_73, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.80/6.41  tff(f_104, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 13.80/6.41  tff(f_60, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 13.80/6.41  tff(f_66, axiom, (![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_enumset1)).
% 13.80/6.41  tff(f_64, axiom, (![A]: (k4_enumset1(A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_enumset1)).
% 13.80/6.41  tff(f_117, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_enumset1(B, C, D), k1_zfmisc_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_subset_1)).
% 13.80/6.41  tff(f_126, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 13.80/6.41  tff(c_110, plain, (![A_71, B_72]: (r1_xboole_0(k4_xboole_0(A_71, B_72), k4_xboole_0(B_72, A_71)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.80/6.41  tff(c_10, plain, (![A_4]: (~r1_xboole_0(A_4, A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.80/6.41  tff(c_115, plain, (![B_72]: (k4_xboole_0(B_72, B_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_10])).
% 13.80/6.41  tff(c_12, plain, (![A_5, B_6]: (r1_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.80/6.41  tff(c_183, plain, (![A_99, B_100, C_101, D_102]: (~r1_xboole_0(A_99, B_100) | r1_xboole_0(k2_zfmisc_1(A_99, C_101), k2_zfmisc_1(B_100, D_102)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.80/6.41  tff(c_190, plain, (![B_106, D_107]: (k2_zfmisc_1(B_106, D_107)=k1_xboole_0 | ~r1_xboole_0(B_106, B_106))), inference(resolution, [status(thm)], [c_183, c_10])).
% 13.80/6.41  tff(c_199, plain, (![B_6, D_107]: (k2_zfmisc_1(k4_xboole_0(B_6, B_6), D_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_190])).
% 13.80/6.41  tff(c_205, plain, (![D_107]: (k2_zfmisc_1(k1_xboole_0, D_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_199])).
% 13.80/6.41  tff(c_207, plain, (![D_108]: (k2_zfmisc_1(k1_xboole_0, D_108)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_199])).
% 13.80/6.41  tff(c_40, plain, (![C_36, A_34, B_35]: (r1_tarski(k2_zfmisc_1(C_36, A_34), k2_zfmisc_1(C_36, B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.80/6.41  tff(c_212, plain, (![B_35, D_108]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(k1_xboole_0, B_35)) | ~r1_tarski(D_108, B_35))), inference(superposition, [status(thm), theory('equality')], [c_207, c_40])).
% 13.80/6.41  tff(c_231, plain, (![D_108, B_35]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(D_108, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_212])).
% 13.80/6.41  tff(c_235, plain, (![D_108, B_35]: (~r1_tarski(D_108, B_35))), inference(splitLeft, [status(thm)], [c_231])).
% 13.80/6.41  tff(c_56, plain, (![A_45]: (v1_xboole_0(k1_subset_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.80/6.41  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 13.80/6.41  tff(c_80, plain, (![B_64, A_65]: (~v1_xboole_0(B_64) | B_64=A_65 | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.80/6.41  tff(c_87, plain, (![A_66]: (o_0_0_xboole_0=A_66 | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_2, c_80])).
% 13.80/6.41  tff(c_94, plain, (![A_45]: (k1_subset_1(A_45)=o_0_0_xboole_0)), inference(resolution, [status(thm)], [c_56, c_87])).
% 13.80/6.41  tff(c_54, plain, (![A_44]: (m1_subset_1(k1_subset_1(A_44), k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.80/6.41  tff(c_58, plain, (![A_46]: (r1_tarski(k1_subset_1(A_46), k3_subset_1(A_46, k1_subset_1(A_46))) | ~m1_subset_1(k1_subset_1(A_46), k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.80/6.41  tff(c_70, plain, (![A_46]: (r1_tarski(k1_subset_1(A_46), k3_subset_1(A_46, k1_subset_1(A_46))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58])).
% 13.80/6.41  tff(c_134, plain, (![A_46]: (r1_tarski(o_0_0_xboole_0, k3_subset_1(A_46, o_0_0_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_70])).
% 13.80/6.41  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_235, c_134])).
% 13.80/6.41  tff(c_243, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_231])).
% 13.80/6.41  tff(c_163, plain, (![A_87, B_88, C_89]: (r1_tarski(A_87, B_88) | ~r1_tarski(A_87, k4_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.80/6.41  tff(c_166, plain, (![A_87, B_72]: (r1_tarski(A_87, B_72) | ~r1_tarski(A_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_163])).
% 13.80/6.41  tff(c_256, plain, (![B_72]: (r1_tarski(k1_xboole_0, B_72))), inference(resolution, [status(thm)], [c_243, c_166])).
% 13.80/6.41  tff(c_116, plain, (![B_73]: (k4_xboole_0(B_73, B_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_10])).
% 13.80/6.41  tff(c_50, plain, (![C_43, B_42]: (~r2_hidden(C_43, k4_xboole_0(B_42, k1_tarski(C_43))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.80/6.41  tff(c_127, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_50])).
% 13.80/6.41  tff(c_889, plain, (![A_192, B_193]: (r1_tarski('#skF_1'(A_192, B_193), A_192) | r2_hidden('#skF_2'(A_192, B_193), B_193) | k1_zfmisc_1(A_192)=B_193)), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.80/6.41  tff(c_925, plain, (![A_194]: (r1_tarski('#skF_1'(A_194, k1_xboole_0), A_194) | k1_zfmisc_1(A_194)=k1_xboole_0)), inference(resolution, [status(thm)], [c_889, c_127])).
% 13.80/6.41  tff(c_152, plain, (![A_81, C_82, B_83]: (r1_xboole_0(A_81, C_82) | ~r1_tarski(A_81, k4_xboole_0(B_83, C_82)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.80/6.41  tff(c_156, plain, (![A_84, B_85]: (r1_xboole_0(A_84, B_85) | ~r1_tarski(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_152])).
% 13.80/6.41  tff(c_161, plain, (![B_85]: (k1_xboole_0=B_85 | ~r1_tarski(B_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_156, c_10])).
% 13.80/6.41  tff(c_951, plain, ('#skF_1'(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_925, c_161])).
% 13.80/6.41  tff(c_953, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_951])).
% 13.80/6.41  tff(c_30, plain, (![C_33, A_29]: (r2_hidden(C_33, k1_zfmisc_1(A_29)) | ~r1_tarski(C_33, A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.80/6.41  tff(c_962, plain, (![C_33]: (r2_hidden(C_33, k1_xboole_0) | ~r1_tarski(C_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_953, c_30])).
% 13.80/6.41  tff(c_969, plain, (![C_195]: (~r1_tarski(C_195, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_127, c_962])).
% 13.80/6.41  tff(c_982, plain, $false, inference(resolution, [status(thm)], [c_256, c_969])).
% 13.80/6.41  tff(c_984, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_951])).
% 13.80/6.41  tff(c_62, plain, (![A_48]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.80/6.41  tff(c_1040, plain, (![E_206, B_209, D_208, F_207, C_205, A_204]: (k6_enumset1(A_204, A_204, A_204, B_209, C_205, D_208, E_206, F_207)=k4_enumset1(A_204, B_209, C_205, D_208, E_206, F_207))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.80/6.41  tff(c_26, plain, (![A_26, B_27, C_28]: (k6_enumset1(A_26, A_26, A_26, A_26, A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.80/6.41  tff(c_1564, plain, (![D_234, E_235, F_236]: (k4_enumset1(D_234, D_234, D_234, D_234, E_235, F_236)=k1_enumset1(D_234, E_235, F_236))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_26])).
% 13.80/6.41  tff(c_24, plain, (![A_25]: (k4_enumset1(A_25, A_25, A_25, A_25, A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.80/6.41  tff(c_1580, plain, (![F_237]: (k1_enumset1(F_237, F_237, F_237)=k1_tarski(F_237))), inference(superposition, [status(thm), theory('equality')], [c_1564, c_24])).
% 13.80/6.41  tff(c_64, plain, (![B_50, C_54, D_56, A_49]: (m1_subset_1(k1_enumset1(B_50, C_54, D_56), k1_zfmisc_1(A_49)) | k1_xboole_0=A_49 | ~m1_subset_1(D_56, A_49) | ~m1_subset_1(C_54, A_49) | ~m1_subset_1(B_50, A_49))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.80/6.41  tff(c_52362, plain, (![F_1155, A_1156]: (m1_subset_1(k1_tarski(F_1155), k1_zfmisc_1(A_1156)) | k1_xboole_0=A_1156 | ~m1_subset_1(F_1155, A_1156) | ~m1_subset_1(F_1155, A_1156) | ~m1_subset_1(F_1155, A_1156))), inference(superposition, [status(thm), theory('equality')], [c_1580, c_64])).
% 13.80/6.41  tff(c_68, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.80/6.41  tff(c_52367, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_52362, c_68])).
% 13.80/6.41  tff(c_52371, plain, (k1_zfmisc_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52367])).
% 13.80/6.41  tff(c_28, plain, (![C_33, A_29]: (r1_tarski(C_33, A_29) | ~r2_hidden(C_33, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.80/6.41  tff(c_2146, plain, (![A_280, A_281]: (r1_tarski('#skF_2'(A_280, k1_zfmisc_1(A_281)), A_281) | r1_tarski('#skF_1'(A_280, k1_zfmisc_1(A_281)), A_280) | k1_zfmisc_1(A_281)=k1_zfmisc_1(A_280))), inference(resolution, [status(thm)], [c_889, c_28])).
% 13.80/6.41  tff(c_6, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.80/6.41  tff(c_27414, plain, (![A_766, B_767, C_768]: (r1_tarski('#skF_2'(A_766, k1_zfmisc_1(k4_xboole_0(B_767, C_768))), B_767) | r1_tarski('#skF_1'(A_766, k1_zfmisc_1(k4_xboole_0(B_767, C_768))), A_766) | k1_zfmisc_1(k4_xboole_0(B_767, C_768))=k1_zfmisc_1(A_766))), inference(resolution, [status(thm)], [c_2146, c_6])).
% 13.80/6.41  tff(c_34, plain, (![A_29, B_30]: (r1_tarski('#skF_1'(A_29, B_30), A_29) | ~r1_tarski('#skF_2'(A_29, B_30), A_29) | k1_zfmisc_1(A_29)=B_30)), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.80/6.41  tff(c_29119, plain, (![B_780, C_781]: (r1_tarski('#skF_1'(B_780, k1_zfmisc_1(k4_xboole_0(B_780, C_781))), B_780) | k1_zfmisc_1(k4_xboole_0(B_780, C_781))=k1_zfmisc_1(B_780))), inference(resolution, [status(thm)], [c_27414, c_34])).
% 13.80/6.41  tff(c_29167, plain, (![B_72]: (r1_tarski('#skF_1'(B_72, k1_zfmisc_1(k1_xboole_0)), B_72) | k1_zfmisc_1(k4_xboole_0(B_72, B_72))=k1_zfmisc_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_115, c_29119])).
% 13.80/6.41  tff(c_29182, plain, (![B_72]: (r1_tarski('#skF_1'(B_72, k1_zfmisc_1(k1_xboole_0)), B_72) | k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_29167])).
% 13.80/6.41  tff(c_52426, plain, (![C_33]: (r2_hidden(C_33, k1_xboole_0) | ~r1_tarski(C_33, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_52371, c_30])).
% 13.80/6.41  tff(c_52449, plain, (![C_1157]: (~r1_tarski(C_1157, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_127, c_52426])).
% 13.80/6.41  tff(c_52511, plain, (k1_zfmisc_1(k1_xboole_0)=k1_zfmisc_1('#skF_3')), inference(resolution, [status(thm)], [c_29182, c_52449])).
% 13.80/6.41  tff(c_52600, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52371, c_52511])).
% 13.80/6.41  tff(c_52602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_984, c_52600])).
% 13.80/6.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.80/6.41  
% 13.80/6.41  Inference rules
% 13.80/6.41  ----------------------
% 13.80/6.41  #Ref     : 0
% 13.80/6.41  #Sup     : 13564
% 13.80/6.41  #Fact    : 0
% 13.80/6.41  #Define  : 0
% 13.80/6.41  #Split   : 5
% 13.80/6.41  #Chain   : 0
% 13.80/6.41  #Close   : 0
% 13.80/6.41  
% 13.80/6.41  Ordering : KBO
% 13.80/6.41  
% 13.80/6.41  Simplification rules
% 13.80/6.41  ----------------------
% 13.80/6.41  #Subsume      : 626
% 13.80/6.41  #Demod        : 17694
% 13.80/6.41  #Tautology    : 9563
% 13.80/6.41  #SimpNegUnit  : 61
% 13.80/6.41  #BackRed      : 12
% 13.80/6.41  
% 13.80/6.41  #Partial instantiations: 0
% 13.80/6.41  #Strategies tried      : 1
% 13.80/6.41  
% 13.80/6.41  Timing (in seconds)
% 13.80/6.41  ----------------------
% 13.80/6.41  Preprocessing        : 0.33
% 13.80/6.41  Parsing              : 0.17
% 13.80/6.41  CNF conversion       : 0.02
% 13.80/6.41  Main loop            : 5.32
% 13.80/6.41  Inferencing          : 1.02
% 13.80/6.41  Reduction            : 1.85
% 13.80/6.41  Demodulation         : 1.48
% 13.80/6.41  BG Simplification    : 0.12
% 13.80/6.41  Subsumption          : 2.04
% 13.80/6.41  Abstraction          : 0.18
% 13.80/6.41  MUC search           : 0.00
% 13.80/6.41  Cooper               : 0.00
% 13.80/6.41  Total                : 5.69
% 13.80/6.41  Index Insertion      : 0.00
% 13.80/6.41  Index Deletion       : 0.00
% 13.80/6.41  Index Matching       : 0.00
% 13.80/6.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
