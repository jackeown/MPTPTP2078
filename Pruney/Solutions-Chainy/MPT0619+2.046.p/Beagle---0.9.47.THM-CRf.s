%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:57 EST 2020

% Result     : Theorem 10.86s
% Output     : CNFRefutation 10.86s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 219 expanded)
%              Number of leaves         :   45 (  96 expanded)
%              Depth                    :   27
%              Number of atoms          :  200 ( 520 expanded)
%              Number of equality atoms :   63 ( 175 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_126,plain,(
    ! [A_95] :
      ( k1_relat_1(A_95) = k1_xboole_0
      | k2_relat_1(A_95) != k1_xboole_0
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_134,plain,
    ( k1_relat_1('#skF_9') = k1_xboole_0
    | k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_126])).

tff(c_135,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_2'(A_32,B_33),A_32)
      | k1_xboole_0 = A_32
      | k1_tarski(B_33) = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_78,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,(
    ! [A_46,C_82] :
      ( r2_hidden('#skF_7'(A_46,k2_relat_1(A_46),C_82),k1_relat_1(A_46))
      | ~ r2_hidden(C_82,k2_relat_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_158,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden('#skF_1'(A_98,B_99),B_99)
      | r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_158])).

tff(c_342,plain,(
    ! [A_157,D_158] :
      ( r2_hidden(k1_funct_1(A_157,D_158),k2_relat_1(A_157))
      | ~ r2_hidden(D_158,k1_relat_1(A_157))
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_351,plain,(
    ! [A_157,D_158,B_2] :
      ( r2_hidden(k1_funct_1(A_157,D_158),B_2)
      | ~ r1_tarski(k2_relat_1(A_157),B_2)
      | ~ r2_hidden(D_158,k1_relat_1(A_157))
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(resolution,[status(thm)],[c_342,c_2])).

tff(c_56,plain,(
    ! [A_46,D_85] :
      ( r2_hidden(k1_funct_1(A_46,D_85),k2_relat_1(A_46))
      | ~ r2_hidden(D_85,k1_relat_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    ! [A_44] :
      ( k2_relat_1(k4_relat_1(A_44)) = k1_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    ! [A_35] :
      ( v1_relat_1(k4_relat_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    ! [A_44] :
      ( k1_relat_1(k4_relat_1(A_44)) = k2_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_165,plain,(
    ! [A_101] :
      ( r1_tarski(A_101,k2_zfmisc_1(k1_relat_1(A_101),k2_relat_1(A_101)))
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_375,plain,(
    ! [A_163] :
      ( r1_tarski(k4_relat_1(A_163),k2_zfmisc_1(k2_relat_1(A_163),k2_relat_1(k4_relat_1(A_163))))
      | ~ v1_relat_1(k4_relat_1(A_163))
      | ~ v1_relat_1(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_165])).

tff(c_387,plain,(
    ! [A_44] :
      ( r1_tarski(k4_relat_1(A_44),k2_zfmisc_1(k2_relat_1(A_44),k1_relat_1(A_44)))
      | ~ v1_relat_1(k4_relat_1(A_44))
      | ~ v1_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_375])).

tff(c_425,plain,(
    ! [A_180,B_181,C_182] :
      ( r2_hidden(k4_tarski('#skF_3'(A_180,B_181,C_182),A_180),C_182)
      | ~ r2_hidden(A_180,k9_relat_1(C_182,B_181))
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_941,plain,(
    ! [A_235,B_236,C_237,B_238] :
      ( r2_hidden(k4_tarski('#skF_3'(A_235,B_236,C_237),A_235),B_238)
      | ~ r1_tarski(C_237,B_238)
      | ~ r2_hidden(A_235,k9_relat_1(C_237,B_236))
      | ~ v1_relat_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_425,c_2])).

tff(c_76,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_186,plain,(
    ! [D_110,B_111,A_112,C_113] :
      ( D_110 = B_111
      | ~ r2_hidden(k4_tarski(A_112,B_111),k2_zfmisc_1(C_113,k1_tarski(D_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_189,plain,(
    ! [B_111,A_112,C_113] :
      ( B_111 = '#skF_8'
      | ~ r2_hidden(k4_tarski(A_112,B_111),k2_zfmisc_1(C_113,k1_relat_1('#skF_9'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_186])).

tff(c_983,plain,(
    ! [A_239,C_240,C_241,B_242] :
      ( A_239 = '#skF_8'
      | ~ r1_tarski(C_240,k2_zfmisc_1(C_241,k1_relat_1('#skF_9')))
      | ~ r2_hidden(A_239,k9_relat_1(C_240,B_242))
      | ~ v1_relat_1(C_240) ) ),
    inference(resolution,[status(thm)],[c_941,c_189])).

tff(c_989,plain,(
    ! [A_239,B_242] :
      ( A_239 = '#skF_8'
      | ~ r2_hidden(A_239,k9_relat_1(k4_relat_1('#skF_9'),B_242))
      | ~ v1_relat_1(k4_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_387,c_983])).

tff(c_1001,plain,(
    ! [A_239,B_242] :
      ( A_239 = '#skF_8'
      | ~ r2_hidden(A_239,k9_relat_1(k4_relat_1('#skF_9'),B_242))
      | ~ v1_relat_1(k4_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_989])).

tff(c_1006,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_1032,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_1006])).

tff(c_1036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1032])).

tff(c_1038,plain,(
    v1_relat_1(k4_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_146,plain,(
    ! [A_97] :
      ( k9_relat_1(A_97,k1_relat_1(A_97)) = k2_relat_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_155,plain,(
    ! [A_44] :
      ( k9_relat_1(k4_relat_1(A_44),k2_relat_1(A_44)) = k2_relat_1(k4_relat_1(A_44))
      | ~ v1_relat_1(k4_relat_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_146])).

tff(c_1047,plain,(
    ! [A_247,B_248] :
      ( A_247 = '#skF_8'
      | ~ r2_hidden(A_247,k9_relat_1(k4_relat_1('#skF_9'),B_248)) ) ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_1091,plain,(
    ! [A_247] :
      ( A_247 = '#skF_8'
      | ~ r2_hidden(A_247,k2_relat_1(k4_relat_1('#skF_9')))
      | ~ v1_relat_1(k4_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_1047])).

tff(c_1131,plain,(
    ! [A_249] :
      ( A_249 = '#skF_8'
      | ~ r2_hidden(A_249,k2_relat_1(k4_relat_1('#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1038,c_1091])).

tff(c_1193,plain,(
    ! [A_249] :
      ( A_249 = '#skF_8'
      | ~ r2_hidden(A_249,k1_relat_1('#skF_9'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1131])).

tff(c_1214,plain,(
    ! [A_250] :
      ( A_250 = '#skF_8'
      | ~ r2_hidden(A_250,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1193])).

tff(c_1250,plain,(
    ! [C_82] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_82) = '#skF_8'
      | ~ r2_hidden(C_82,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_1214])).

tff(c_1436,plain,(
    ! [C_259] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_259) = '#skF_8'
      | ~ r2_hidden(C_259,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1250])).

tff(c_1476,plain,(
    ! [D_85] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_85)) = '#skF_8'
      | ~ r2_hidden(D_85,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56,c_1436])).

tff(c_1911,plain,(
    ! [D_285] :
      ( '#skF_7'('#skF_9',k2_relat_1('#skF_9'),k1_funct_1('#skF_9',D_285)) = '#skF_8'
      | ~ r2_hidden(D_285,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1476])).

tff(c_58,plain,(
    ! [A_46,C_82] :
      ( k1_funct_1(A_46,'#skF_7'(A_46,k2_relat_1(A_46),C_82)) = C_82
      | ~ r2_hidden(C_82,k2_relat_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1917,plain,(
    ! [D_285] :
      ( k1_funct_1('#skF_9',D_285) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_285),k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_285,k1_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1911,c_58])).

tff(c_21205,plain,(
    ! [D_36578] :
      ( k1_funct_1('#skF_9',D_36578) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9',D_36578),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_36578,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1917])).

tff(c_21222,plain,(
    ! [D_158] :
      ( k1_funct_1('#skF_9',D_158) = k1_funct_1('#skF_9','#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_9'),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_158,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_351,c_21205])).

tff(c_21239,plain,(
    ! [D_36744] :
      ( k1_funct_1('#skF_9',D_36744) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(D_36744,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_163,c_21222])).

tff(c_21334,plain,(
    ! [C_82] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_82)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_82,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_60,c_21239])).

tff(c_22204,plain,(
    ! [C_37579] :
      ( k1_funct_1('#skF_9','#skF_7'('#skF_9',k2_relat_1('#skF_9'),C_37579)) = k1_funct_1('#skF_9','#skF_8')
      | ~ r2_hidden(C_37579,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_21334])).

tff(c_22229,plain,(
    ! [C_37579] :
      ( k1_funct_1('#skF_9','#skF_8') = C_37579
      | ~ r2_hidden(C_37579,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_37579,k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22204,c_58])).

tff(c_22295,plain,(
    ! [C_37745] :
      ( k1_funct_1('#skF_9','#skF_8') = C_37745
      | ~ r2_hidden(C_37745,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_22229])).

tff(c_22410,plain,(
    ! [B_33] :
      ( '#skF_2'(k2_relat_1('#skF_9'),B_33) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_33) ) ),
    inference(resolution,[status(thm)],[c_32,c_22295])).

tff(c_22572,plain,(
    ! [B_38077] :
      ( '#skF_2'(k2_relat_1('#skF_9'),B_38077) = k1_funct_1('#skF_9','#skF_8')
      | k2_relat_1('#skF_9') = k1_tarski(B_38077) ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_22410])).

tff(c_30,plain,(
    ! [A_32,B_33] :
      ( '#skF_2'(A_32,B_33) != B_33
      | k1_xboole_0 = A_32
      | k1_tarski(B_33) = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22599,plain,(
    ! [B_38077] :
      ( k1_funct_1('#skF_9','#skF_8') != B_38077
      | k2_relat_1('#skF_9') = k1_xboole_0
      | k2_relat_1('#skF_9') = k1_tarski(B_38077)
      | k2_relat_1('#skF_9') = k1_tarski(B_38077) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22572,c_30])).

tff(c_22646,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) = k2_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_22599])).

tff(c_74,plain,(
    k1_tarski(k1_funct_1('#skF_9','#skF_8')) != k2_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22646,c_74])).

tff(c_22650,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_22,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_tarski(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_22])).

tff(c_22661,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22650,c_84])).

tff(c_22665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.86/3.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/3.99  
% 10.86/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/3.99  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 10.86/3.99  
% 10.86/3.99  %Foreground sorts:
% 10.86/3.99  
% 10.86/3.99  
% 10.86/3.99  %Background operators:
% 10.86/3.99  
% 10.86/3.99  
% 10.86/3.99  %Foreground operators:
% 10.86/3.99  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.86/3.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.86/3.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.86/3.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.86/3.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.86/3.99  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.86/3.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.86/3.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.86/3.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.86/3.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.86/3.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.86/3.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.86/3.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.86/3.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.86/3.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.86/3.99  tff('#skF_9', type, '#skF_9': $i).
% 10.86/3.99  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 10.86/3.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.86/3.99  tff('#skF_8', type, '#skF_8': $i).
% 10.86/3.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.86/3.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.86/3.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.86/3.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.86/3.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.86/3.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.86/3.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.86/3.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.86/3.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.86/3.99  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.86/3.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.86/3.99  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.86/3.99  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.86/3.99  
% 10.86/4.01  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.86/4.01  tff(f_127, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 10.86/4.01  tff(f_103, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 10.86/4.01  tff(f_68, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 10.86/4.01  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 10.86/4.01  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.86/4.01  tff(f_97, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 10.86/4.01  tff(f_72, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 10.86/4.01  tff(f_91, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 10.86/4.01  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 10.86/4.01  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 10.86/4.01  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 10.86/4.01  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 10.86/4.01  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.86/4.01  tff(c_80, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.86/4.01  tff(c_126, plain, (![A_95]: (k1_relat_1(A_95)=k1_xboole_0 | k2_relat_1(A_95)!=k1_xboole_0 | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.86/4.01  tff(c_134, plain, (k1_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_126])).
% 10.86/4.01  tff(c_135, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_134])).
% 10.86/4.01  tff(c_32, plain, (![A_32, B_33]: (r2_hidden('#skF_2'(A_32, B_33), A_32) | k1_xboole_0=A_32 | k1_tarski(B_33)=A_32)), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.86/4.01  tff(c_78, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.86/4.01  tff(c_60, plain, (![A_46, C_82]: (r2_hidden('#skF_7'(A_46, k2_relat_1(A_46), C_82), k1_relat_1(A_46)) | ~r2_hidden(C_82, k2_relat_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.86/4.01  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.86/4.01  tff(c_158, plain, (![A_98, B_99]: (~r2_hidden('#skF_1'(A_98, B_99), B_99) | r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.86/4.01  tff(c_163, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_158])).
% 10.86/4.01  tff(c_342, plain, (![A_157, D_158]: (r2_hidden(k1_funct_1(A_157, D_158), k2_relat_1(A_157)) | ~r2_hidden(D_158, k1_relat_1(A_157)) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.86/4.01  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.86/4.01  tff(c_351, plain, (![A_157, D_158, B_2]: (r2_hidden(k1_funct_1(A_157, D_158), B_2) | ~r1_tarski(k2_relat_1(A_157), B_2) | ~r2_hidden(D_158, k1_relat_1(A_157)) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(resolution, [status(thm)], [c_342, c_2])).
% 10.86/4.01  tff(c_56, plain, (![A_46, D_85]: (r2_hidden(k1_funct_1(A_46, D_85), k2_relat_1(A_46)) | ~r2_hidden(D_85, k1_relat_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.86/4.01  tff(c_48, plain, (![A_44]: (k2_relat_1(k4_relat_1(A_44))=k1_relat_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.86/4.01  tff(c_34, plain, (![A_35]: (v1_relat_1(k4_relat_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.86/4.01  tff(c_50, plain, (![A_44]: (k1_relat_1(k4_relat_1(A_44))=k2_relat_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.86/4.01  tff(c_165, plain, (![A_101]: (r1_tarski(A_101, k2_zfmisc_1(k1_relat_1(A_101), k2_relat_1(A_101))) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.86/4.01  tff(c_375, plain, (![A_163]: (r1_tarski(k4_relat_1(A_163), k2_zfmisc_1(k2_relat_1(A_163), k2_relat_1(k4_relat_1(A_163)))) | ~v1_relat_1(k4_relat_1(A_163)) | ~v1_relat_1(A_163))), inference(superposition, [status(thm), theory('equality')], [c_50, c_165])).
% 10.86/4.01  tff(c_387, plain, (![A_44]: (r1_tarski(k4_relat_1(A_44), k2_zfmisc_1(k2_relat_1(A_44), k1_relat_1(A_44))) | ~v1_relat_1(k4_relat_1(A_44)) | ~v1_relat_1(A_44) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_48, c_375])).
% 10.86/4.01  tff(c_425, plain, (![A_180, B_181, C_182]: (r2_hidden(k4_tarski('#skF_3'(A_180, B_181, C_182), A_180), C_182) | ~r2_hidden(A_180, k9_relat_1(C_182, B_181)) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.86/4.01  tff(c_941, plain, (![A_235, B_236, C_237, B_238]: (r2_hidden(k4_tarski('#skF_3'(A_235, B_236, C_237), A_235), B_238) | ~r1_tarski(C_237, B_238) | ~r2_hidden(A_235, k9_relat_1(C_237, B_236)) | ~v1_relat_1(C_237))), inference(resolution, [status(thm)], [c_425, c_2])).
% 10.86/4.01  tff(c_76, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.86/4.01  tff(c_186, plain, (![D_110, B_111, A_112, C_113]: (D_110=B_111 | ~r2_hidden(k4_tarski(A_112, B_111), k2_zfmisc_1(C_113, k1_tarski(D_110))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.86/4.01  tff(c_189, plain, (![B_111, A_112, C_113]: (B_111='#skF_8' | ~r2_hidden(k4_tarski(A_112, B_111), k2_zfmisc_1(C_113, k1_relat_1('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_76, c_186])).
% 10.86/4.01  tff(c_983, plain, (![A_239, C_240, C_241, B_242]: (A_239='#skF_8' | ~r1_tarski(C_240, k2_zfmisc_1(C_241, k1_relat_1('#skF_9'))) | ~r2_hidden(A_239, k9_relat_1(C_240, B_242)) | ~v1_relat_1(C_240))), inference(resolution, [status(thm)], [c_941, c_189])).
% 10.86/4.01  tff(c_989, plain, (![A_239, B_242]: (A_239='#skF_8' | ~r2_hidden(A_239, k9_relat_1(k4_relat_1('#skF_9'), B_242)) | ~v1_relat_1(k4_relat_1('#skF_9')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_387, c_983])).
% 10.86/4.01  tff(c_1001, plain, (![A_239, B_242]: (A_239='#skF_8' | ~r2_hidden(A_239, k9_relat_1(k4_relat_1('#skF_9'), B_242)) | ~v1_relat_1(k4_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_989])).
% 10.86/4.01  tff(c_1006, plain, (~v1_relat_1(k4_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_1001])).
% 10.86/4.01  tff(c_1032, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_34, c_1006])).
% 10.86/4.01  tff(c_1036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_1032])).
% 10.86/4.01  tff(c_1038, plain, (v1_relat_1(k4_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_1001])).
% 10.86/4.01  tff(c_146, plain, (![A_97]: (k9_relat_1(A_97, k1_relat_1(A_97))=k2_relat_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.86/4.01  tff(c_155, plain, (![A_44]: (k9_relat_1(k4_relat_1(A_44), k2_relat_1(A_44))=k2_relat_1(k4_relat_1(A_44)) | ~v1_relat_1(k4_relat_1(A_44)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_50, c_146])).
% 10.86/4.01  tff(c_1047, plain, (![A_247, B_248]: (A_247='#skF_8' | ~r2_hidden(A_247, k9_relat_1(k4_relat_1('#skF_9'), B_248)))), inference(splitRight, [status(thm)], [c_1001])).
% 10.86/4.01  tff(c_1091, plain, (![A_247]: (A_247='#skF_8' | ~r2_hidden(A_247, k2_relat_1(k4_relat_1('#skF_9'))) | ~v1_relat_1(k4_relat_1('#skF_9')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_1047])).
% 10.86/4.01  tff(c_1131, plain, (![A_249]: (A_249='#skF_8' | ~r2_hidden(A_249, k2_relat_1(k4_relat_1('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1038, c_1091])).
% 10.86/4.01  tff(c_1193, plain, (![A_249]: (A_249='#skF_8' | ~r2_hidden(A_249, k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1131])).
% 10.86/4.01  tff(c_1214, plain, (![A_250]: (A_250='#skF_8' | ~r2_hidden(A_250, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1193])).
% 10.86/4.01  tff(c_1250, plain, (![C_82]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_82)='#skF_8' | ~r2_hidden(C_82, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_60, c_1214])).
% 10.86/4.01  tff(c_1436, plain, (![C_259]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_259)='#skF_8' | ~r2_hidden(C_259, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1250])).
% 10.86/4.01  tff(c_1476, plain, (![D_85]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_85))='#skF_8' | ~r2_hidden(D_85, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_56, c_1436])).
% 10.86/4.01  tff(c_1911, plain, (![D_285]: ('#skF_7'('#skF_9', k2_relat_1('#skF_9'), k1_funct_1('#skF_9', D_285))='#skF_8' | ~r2_hidden(D_285, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1476])).
% 10.86/4.01  tff(c_58, plain, (![A_46, C_82]: (k1_funct_1(A_46, '#skF_7'(A_46, k2_relat_1(A_46), C_82))=C_82 | ~r2_hidden(C_82, k2_relat_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.86/4.01  tff(c_1917, plain, (![D_285]: (k1_funct_1('#skF_9', D_285)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_285), k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_285, k1_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1911, c_58])).
% 10.86/4.01  tff(c_21205, plain, (![D_36578]: (k1_funct_1('#skF_9', D_36578)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', D_36578), k2_relat_1('#skF_9')) | ~r2_hidden(D_36578, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1917])).
% 10.86/4.01  tff(c_21222, plain, (![D_158]: (k1_funct_1('#skF_9', D_158)=k1_funct_1('#skF_9', '#skF_8') | ~r1_tarski(k2_relat_1('#skF_9'), k2_relat_1('#skF_9')) | ~r2_hidden(D_158, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_351, c_21205])).
% 10.86/4.01  tff(c_21239, plain, (![D_36744]: (k1_funct_1('#skF_9', D_36744)=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(D_36744, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_163, c_21222])).
% 10.86/4.01  tff(c_21334, plain, (![C_82]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_82))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_82, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_60, c_21239])).
% 10.86/4.01  tff(c_22204, plain, (![C_37579]: (k1_funct_1('#skF_9', '#skF_7'('#skF_9', k2_relat_1('#skF_9'), C_37579))=k1_funct_1('#skF_9', '#skF_8') | ~r2_hidden(C_37579, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_21334])).
% 10.86/4.01  tff(c_22229, plain, (![C_37579]: (k1_funct_1('#skF_9', '#skF_8')=C_37579 | ~r2_hidden(C_37579, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_37579, k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_22204, c_58])).
% 10.86/4.01  tff(c_22295, plain, (![C_37745]: (k1_funct_1('#skF_9', '#skF_8')=C_37745 | ~r2_hidden(C_37745, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_22229])).
% 10.86/4.01  tff(c_22410, plain, (![B_33]: ('#skF_2'(k2_relat_1('#skF_9'), B_33)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_33))), inference(resolution, [status(thm)], [c_32, c_22295])).
% 10.86/4.01  tff(c_22572, plain, (![B_38077]: ('#skF_2'(k2_relat_1('#skF_9'), B_38077)=k1_funct_1('#skF_9', '#skF_8') | k2_relat_1('#skF_9')=k1_tarski(B_38077))), inference(negUnitSimplification, [status(thm)], [c_135, c_22410])).
% 10.86/4.01  tff(c_30, plain, (![A_32, B_33]: ('#skF_2'(A_32, B_33)!=B_33 | k1_xboole_0=A_32 | k1_tarski(B_33)=A_32)), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.86/4.01  tff(c_22599, plain, (![B_38077]: (k1_funct_1('#skF_9', '#skF_8')!=B_38077 | k2_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')=k1_tarski(B_38077) | k2_relat_1('#skF_9')=k1_tarski(B_38077))), inference(superposition, [status(thm), theory('equality')], [c_22572, c_30])).
% 10.86/4.01  tff(c_22646, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))=k2_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_135, c_22599])).
% 10.86/4.01  tff(c_74, plain, (k1_tarski(k1_funct_1('#skF_9', '#skF_8'))!=k2_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.86/4.01  tff(c_22649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22646, c_74])).
% 10.86/4.01  tff(c_22650, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_134])).
% 10.86/4.01  tff(c_22, plain, (![A_27]: (~v1_xboole_0(k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.86/4.01  tff(c_84, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_22])).
% 10.86/4.01  tff(c_22661, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22650, c_84])).
% 10.86/4.01  tff(c_22665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_22661])).
% 10.86/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.86/4.01  
% 10.86/4.01  Inference rules
% 10.86/4.01  ----------------------
% 10.86/4.01  #Ref     : 1
% 10.86/4.01  #Sup     : 4799
% 10.86/4.01  #Fact    : 10
% 10.86/4.01  #Define  : 0
% 10.86/4.01  #Split   : 22
% 10.86/4.01  #Chain   : 0
% 10.86/4.01  #Close   : 0
% 10.86/4.01  
% 10.86/4.01  Ordering : KBO
% 10.86/4.01  
% 10.86/4.01  Simplification rules
% 10.86/4.01  ----------------------
% 10.86/4.01  #Subsume      : 1223
% 10.86/4.01  #Demod        : 961
% 10.86/4.01  #Tautology    : 675
% 10.86/4.01  #SimpNegUnit  : 355
% 10.86/4.01  #BackRed      : 88
% 10.86/4.01  
% 10.86/4.01  #Partial instantiations: 16416
% 10.86/4.01  #Strategies tried      : 1
% 10.86/4.01  
% 10.86/4.01  Timing (in seconds)
% 10.86/4.01  ----------------------
% 10.86/4.01  Preprocessing        : 0.35
% 10.86/4.01  Parsing              : 0.18
% 10.86/4.01  CNF conversion       : 0.03
% 10.86/4.01  Main loop            : 2.87
% 10.86/4.01  Inferencing          : 0.92
% 10.86/4.02  Reduction            : 0.75
% 10.86/4.02  Demodulation         : 0.49
% 10.86/4.02  BG Simplification    : 0.10
% 10.86/4.02  Subsumption          : 0.89
% 10.86/4.02  Abstraction          : 0.13
% 10.86/4.02  MUC search           : 0.00
% 10.86/4.02  Cooper               : 0.00
% 10.86/4.02  Total                : 3.26
% 10.86/4.02  Index Insertion      : 0.00
% 10.86/4.02  Index Deletion       : 0.00
% 10.86/4.02  Index Matching       : 0.00
% 10.86/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
