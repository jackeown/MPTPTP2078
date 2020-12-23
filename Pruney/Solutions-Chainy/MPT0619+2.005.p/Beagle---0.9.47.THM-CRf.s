%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:52 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 220 expanded)
%              Number of leaves         :   40 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          :  131 ( 437 expanded)
%              Number of equality atoms :   56 ( 178 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_76,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_106,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_66,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_63,B_64] :
      ( r2_hidden(A_63,B_64)
      | ~ r1_tarski(k1_tarski(A_63),B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,(
    ! [A_65] : r2_hidden(A_65,k1_tarski(A_65)) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_135,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_132])).

tff(c_56,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(k6_relat_1(A_48),B_49) = k7_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_38,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,(
    ! [A_47] : k2_relat_1(k6_relat_1(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_115,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    ! [B_62] :
      ( r1_tarski(k1_relat_1('#skF_3'),B_62)
      | ~ r2_hidden('#skF_2',B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_115])).

tff(c_1144,plain,(
    ! [B_170,A_171] :
      ( k2_relat_1(k5_relat_1(B_170,A_171)) = k2_relat_1(A_171)
      | ~ r1_tarski(k1_relat_1(A_171),k2_relat_1(B_170))
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1151,plain,(
    ! [B_170] :
      ( k2_relat_1(k5_relat_1(B_170,'#skF_3')) = k2_relat_1('#skF_3')
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1('#skF_3')
      | ~ r2_hidden('#skF_2',k2_relat_1(B_170)) ) ),
    inference(resolution,[status(thm)],[c_118,c_1144])).

tff(c_1681,plain,(
    ! [B_193] :
      ( k2_relat_1(k5_relat_1(B_193,'#skF_3')) = k2_relat_1('#skF_3')
      | ~ v1_relat_1(B_193)
      | ~ r2_hidden('#skF_2',k2_relat_1(B_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1151])).

tff(c_1697,plain,(
    ! [A_47] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_47),'#skF_3')) = k2_relat_1('#skF_3')
      | ~ v1_relat_1(k6_relat_1(A_47))
      | ~ r2_hidden('#skF_2',A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1681])).

tff(c_1700,plain,(
    ! [A_194] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_194),'#skF_3')) = k2_relat_1('#skF_3')
      | ~ r2_hidden('#skF_2',A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1697])).

tff(c_1723,plain,(
    ! [A_48] :
      ( k2_relat_1(k7_relat_1('#skF_3',A_48)) = k2_relat_1('#skF_3')
      | ~ r2_hidden('#skF_2',A_48)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1700])).

tff(c_1734,plain,(
    ! [A_195] :
      ( k2_relat_1(k7_relat_1('#skF_3',A_195)) = k2_relat_1('#skF_3')
      | ~ r2_hidden('#skF_2',A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1723])).

tff(c_40,plain,(
    ! [B_38,A_37] :
      ( k2_relat_1(k7_relat_1(B_38,A_37)) = k9_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1746,plain,(
    ! [A_195] :
      ( k9_relat_1('#skF_3',A_195) = k2_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r2_hidden('#skF_2',A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_40])).

tff(c_1807,plain,(
    ! [A_198] :
      ( k9_relat_1('#skF_3',A_198) = k2_relat_1('#skF_3')
      | ~ r2_hidden('#skF_2',A_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1746])).

tff(c_1869,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_1807])).

tff(c_272,plain,(
    ! [A_92,B_93] :
      ( k9_relat_1(A_92,k1_tarski(B_93)) = k11_relat_1(A_92,B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_281,plain,(
    ! [A_92] :
      ( k9_relat_1(A_92,k1_relat_1('#skF_3')) = k11_relat_1(A_92,'#skF_2')
      | ~ v1_relat_1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_272])).

tff(c_1875,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_281])).

tff(c_1882,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1875])).

tff(c_293,plain,(
    ! [B_95,A_96] :
      ( k11_relat_1(B_95,A_96) != k1_xboole_0
      | ~ r2_hidden(A_96,k1_relat_1(B_95))
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_296,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_293])).

tff(c_302,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_296])).

tff(c_1886,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_302])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | k1_xboole_0 = A_30
      | k1_tarski(B_31) = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(k4_tarski(A_39,B_40),C_41)
      | ~ r2_hidden(B_40,k11_relat_1(C_41,A_39))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_649,plain,(
    ! [C_131,A_132,B_133] :
      ( k1_funct_1(C_131,A_132) = B_133
      | ~ r2_hidden(k4_tarski(A_132,B_133),C_131)
      | ~ v1_funct_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_674,plain,(
    ! [C_41,A_39,B_40] :
      ( k1_funct_1(C_41,A_39) = B_40
      | ~ v1_funct_1(C_41)
      | ~ r2_hidden(B_40,k11_relat_1(C_41,A_39))
      | ~ v1_relat_1(C_41) ) ),
    inference(resolution,[status(thm)],[c_42,c_649])).

tff(c_1895,plain,(
    ! [B_40] :
      ( k1_funct_1('#skF_3','#skF_2') = B_40
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_40,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_674])).

tff(c_2058,plain,(
    ! [B_206] :
      ( k1_funct_1('#skF_3','#skF_2') = B_206
      | ~ r2_hidden(B_206,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1895])).

tff(c_2077,plain,(
    ! [B_31] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_31) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_31) ) ),
    inference(resolution,[status(thm)],[c_34,c_2058])).

tff(c_2468,plain,(
    ! [B_226] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_226) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_226) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1886,c_2077])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( '#skF_1'(A_30,B_31) != B_31
      | k1_xboole_0 = A_30
      | k1_tarski(B_31) = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2476,plain,(
    ! [B_226] :
      ( k1_funct_1('#skF_3','#skF_2') != B_226
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_226)
      | k2_relat_1('#skF_3') = k1_tarski(B_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2468,c_32])).

tff(c_3711,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1886,c_2476])).

tff(c_64,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3711,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.90  
% 4.69/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.90  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.69/1.90  
% 4.69/1.90  %Foreground sorts:
% 4.69/1.90  
% 4.69/1.90  
% 4.69/1.90  %Background operators:
% 4.69/1.90  
% 4.69/1.90  
% 4.69/1.90  %Foreground operators:
% 4.69/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.69/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.69/1.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.69/1.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.69/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.69/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.69/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.69/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.69/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.69/1.90  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.69/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.69/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.90  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.69/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.69/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.69/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.69/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.69/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.69/1.90  
% 4.69/1.92  tff(f_129, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.69/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.69/1.92  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.69/1.92  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.69/1.92  tff(f_76, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.69/1.92  tff(f_106, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.69/1.92  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 4.69/1.92  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.69/1.92  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 4.69/1.92  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.69/1.92  tff(f_69, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 4.69/1.92  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.69/1.92  tff(f_120, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.69/1.92  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.92  tff(c_66, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.92  tff(c_119, plain, (![A_63, B_64]: (r2_hidden(A_63, B_64) | ~r1_tarski(k1_tarski(A_63), B_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.69/1.92  tff(c_132, plain, (![A_65]: (r2_hidden(A_65, k1_tarski(A_65)))), inference(resolution, [status(thm)], [c_6, c_119])).
% 4.69/1.92  tff(c_135, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_132])).
% 4.69/1.92  tff(c_56, plain, (![A_48, B_49]: (k5_relat_1(k6_relat_1(A_48), B_49)=k7_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.69/1.92  tff(c_38, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.69/1.92  tff(c_54, plain, (![A_47]: (k2_relat_1(k6_relat_1(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.69/1.92  tff(c_115, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.69/1.92  tff(c_118, plain, (![B_62]: (r1_tarski(k1_relat_1('#skF_3'), B_62) | ~r2_hidden('#skF_2', B_62))), inference(superposition, [status(thm), theory('equality')], [c_66, c_115])).
% 4.69/1.92  tff(c_1144, plain, (![B_170, A_171]: (k2_relat_1(k5_relat_1(B_170, A_171))=k2_relat_1(A_171) | ~r1_tarski(k1_relat_1(A_171), k2_relat_1(B_170)) | ~v1_relat_1(B_170) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.69/1.92  tff(c_1151, plain, (![B_170]: (k2_relat_1(k5_relat_1(B_170, '#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1(B_170) | ~v1_relat_1('#skF_3') | ~r2_hidden('#skF_2', k2_relat_1(B_170)))), inference(resolution, [status(thm)], [c_118, c_1144])).
% 4.69/1.92  tff(c_1681, plain, (![B_193]: (k2_relat_1(k5_relat_1(B_193, '#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1(B_193) | ~r2_hidden('#skF_2', k2_relat_1(B_193)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1151])).
% 4.69/1.92  tff(c_1697, plain, (![A_47]: (k2_relat_1(k5_relat_1(k6_relat_1(A_47), '#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1(A_47)) | ~r2_hidden('#skF_2', A_47))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1681])).
% 4.69/1.92  tff(c_1700, plain, (![A_194]: (k2_relat_1(k5_relat_1(k6_relat_1(A_194), '#skF_3'))=k2_relat_1('#skF_3') | ~r2_hidden('#skF_2', A_194))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1697])).
% 4.69/1.92  tff(c_1723, plain, (![A_48]: (k2_relat_1(k7_relat_1('#skF_3', A_48))=k2_relat_1('#skF_3') | ~r2_hidden('#skF_2', A_48) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1700])).
% 4.69/1.92  tff(c_1734, plain, (![A_195]: (k2_relat_1(k7_relat_1('#skF_3', A_195))=k2_relat_1('#skF_3') | ~r2_hidden('#skF_2', A_195))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1723])).
% 4.69/1.92  tff(c_40, plain, (![B_38, A_37]: (k2_relat_1(k7_relat_1(B_38, A_37))=k9_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.69/1.92  tff(c_1746, plain, (![A_195]: (k9_relat_1('#skF_3', A_195)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r2_hidden('#skF_2', A_195))), inference(superposition, [status(thm), theory('equality')], [c_1734, c_40])).
% 4.69/1.92  tff(c_1807, plain, (![A_198]: (k9_relat_1('#skF_3', A_198)=k2_relat_1('#skF_3') | ~r2_hidden('#skF_2', A_198))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1746])).
% 4.69/1.92  tff(c_1869, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_1807])).
% 4.69/1.92  tff(c_272, plain, (![A_92, B_93]: (k9_relat_1(A_92, k1_tarski(B_93))=k11_relat_1(A_92, B_93) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.69/1.92  tff(c_281, plain, (![A_92]: (k9_relat_1(A_92, k1_relat_1('#skF_3'))=k11_relat_1(A_92, '#skF_2') | ~v1_relat_1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_66, c_272])).
% 4.69/1.92  tff(c_1875, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1869, c_281])).
% 4.69/1.92  tff(c_1882, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1875])).
% 4.69/1.92  tff(c_293, plain, (![B_95, A_96]: (k11_relat_1(B_95, A_96)!=k1_xboole_0 | ~r2_hidden(A_96, k1_relat_1(B_95)) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.69/1.92  tff(c_296, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_293])).
% 4.69/1.92  tff(c_302, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_296])).
% 4.69/1.92  tff(c_1886, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_302])).
% 4.69/1.92  tff(c_34, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | k1_xboole_0=A_30 | k1_tarski(B_31)=A_30)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.69/1.92  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.92  tff(c_42, plain, (![A_39, B_40, C_41]: (r2_hidden(k4_tarski(A_39, B_40), C_41) | ~r2_hidden(B_40, k11_relat_1(C_41, A_39)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.69/1.92  tff(c_649, plain, (![C_131, A_132, B_133]: (k1_funct_1(C_131, A_132)=B_133 | ~r2_hidden(k4_tarski(A_132, B_133), C_131) | ~v1_funct_1(C_131) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.92  tff(c_674, plain, (![C_41, A_39, B_40]: (k1_funct_1(C_41, A_39)=B_40 | ~v1_funct_1(C_41) | ~r2_hidden(B_40, k11_relat_1(C_41, A_39)) | ~v1_relat_1(C_41))), inference(resolution, [status(thm)], [c_42, c_649])).
% 4.69/1.92  tff(c_1895, plain, (![B_40]: (k1_funct_1('#skF_3', '#skF_2')=B_40 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_40, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1882, c_674])).
% 4.69/1.92  tff(c_2058, plain, (![B_206]: (k1_funct_1('#skF_3', '#skF_2')=B_206 | ~r2_hidden(B_206, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1895])).
% 4.69/1.92  tff(c_2077, plain, (![B_31]: ('#skF_1'(k2_relat_1('#skF_3'), B_31)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_31))), inference(resolution, [status(thm)], [c_34, c_2058])).
% 4.69/1.92  tff(c_2468, plain, (![B_226]: ('#skF_1'(k2_relat_1('#skF_3'), B_226)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_226))), inference(negUnitSimplification, [status(thm)], [c_1886, c_2077])).
% 4.69/1.92  tff(c_32, plain, (![A_30, B_31]: ('#skF_1'(A_30, B_31)!=B_31 | k1_xboole_0=A_30 | k1_tarski(B_31)=A_30)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.69/1.92  tff(c_2476, plain, (![B_226]: (k1_funct_1('#skF_3', '#skF_2')!=B_226 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_226) | k2_relat_1('#skF_3')=k1_tarski(B_226))), inference(superposition, [status(thm), theory('equality')], [c_2468, c_32])).
% 4.69/1.92  tff(c_3711, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1886, c_2476])).
% 4.69/1.92  tff(c_64, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.92  tff(c_3714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3711, c_64])).
% 4.69/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.92  
% 4.69/1.92  Inference rules
% 4.69/1.92  ----------------------
% 4.69/1.92  #Ref     : 0
% 4.69/1.92  #Sup     : 763
% 4.69/1.92  #Fact    : 1
% 4.69/1.92  #Define  : 0
% 4.69/1.92  #Split   : 5
% 4.69/1.92  #Chain   : 0
% 4.69/1.92  #Close   : 0
% 4.69/1.92  
% 4.69/1.92  Ordering : KBO
% 4.69/1.92  
% 4.69/1.92  Simplification rules
% 4.69/1.92  ----------------------
% 4.69/1.92  #Subsume      : 189
% 4.69/1.92  #Demod        : 485
% 4.69/1.92  #Tautology    : 249
% 4.69/1.92  #SimpNegUnit  : 144
% 4.69/1.92  #BackRed      : 2
% 4.69/1.92  
% 4.69/1.92  #Partial instantiations: 0
% 4.69/1.92  #Strategies tried      : 1
% 4.69/1.92  
% 4.69/1.92  Timing (in seconds)
% 4.69/1.92  ----------------------
% 4.69/1.92  Preprocessing        : 0.36
% 4.69/1.92  Parsing              : 0.19
% 4.69/1.92  CNF conversion       : 0.02
% 4.69/1.92  Main loop            : 0.80
% 4.69/1.92  Inferencing          : 0.27
% 4.69/1.92  Reduction            : 0.27
% 4.69/1.92  Demodulation         : 0.19
% 4.69/1.92  BG Simplification    : 0.03
% 4.69/1.92  Subsumption          : 0.16
% 4.69/1.92  Abstraction          : 0.04
% 4.69/1.92  MUC search           : 0.00
% 4.69/1.92  Cooper               : 0.00
% 4.69/1.92  Total                : 1.19
% 4.69/1.92  Index Insertion      : 0.00
% 4.69/1.92  Index Deletion       : 0.00
% 4.69/1.92  Index Matching       : 0.00
% 4.69/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
