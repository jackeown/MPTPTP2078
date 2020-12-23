%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:26 EST 2020

% Result     : Theorem 10.60s
% Output     : CNFRefutation 10.60s
% Verified   : 
% Statistics : Number of formulae       :  130 (1315 expanded)
%              Number of leaves         :   40 ( 470 expanded)
%              Depth                    :   30
%              Number of atoms          :  265 (3411 expanded)
%              Number of equality atoms :   63 ( 767 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_68,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_70,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_58,plain,(
    k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_62,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    ! [B_44,A_43] :
      ( k9_relat_1(k2_funct_1(B_44),A_43) = k10_relat_1(B_44,A_43)
      | ~ v2_funct_1(B_44)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    ! [A_36] :
      ( v1_relat_1(k2_funct_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,k10_relat_1(B_38,k9_relat_1(B_38,A_37)))
      | ~ r1_tarski(A_37,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k10_relat_1(B_32,A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_144,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_853,plain,(
    ! [B_167,A_168] :
      ( k10_relat_1(B_167,A_168) = k1_relat_1(B_167)
      | ~ r1_tarski(k1_relat_1(B_167),k10_relat_1(B_167,A_168))
      | ~ v1_relat_1(B_167) ) ),
    inference(resolution,[status(thm)],[c_42,c_144])).

tff(c_867,plain,(
    ! [B_38] :
      ( k10_relat_1(B_38,k9_relat_1(B_38,k1_relat_1(B_38))) = k1_relat_1(B_38)
      | ~ r1_tarski(k1_relat_1(B_38),k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_50,c_853])).

tff(c_874,plain,(
    ! [B_38] :
      ( k10_relat_1(B_38,k9_relat_1(B_38,k1_relat_1(B_38))) = k1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_867])).

tff(c_24,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_929,plain,(
    ! [B_170,A_171] :
      ( k9_relat_1(B_170,k10_relat_1(B_170,A_171)) = A_171
      | ~ r1_tarski(A_171,k2_relat_1(B_170))
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_941,plain,(
    ! [B_172] :
      ( k9_relat_1(B_172,k10_relat_1(B_172,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(resolution,[status(thm)],[c_24,c_929])).

tff(c_311,plain,(
    ! [B_88,A_89] :
      ( k9_relat_1(B_88,A_89) != k1_xboole_0
      | ~ r1_tarski(A_89,k1_relat_1(B_88))
      | k1_xboole_0 = A_89
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_332,plain,(
    ! [B_32,A_31] :
      ( k9_relat_1(B_32,k10_relat_1(B_32,A_31)) != k1_xboole_0
      | k10_relat_1(B_32,A_31) = k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_42,c_311])).

tff(c_988,plain,(
    ! [B_173] :
      ( k10_relat_1(B_173,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_332])).

tff(c_994,plain,
    ( k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_988])).

tff(c_998,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_994])).

tff(c_1392,plain,(
    ! [C_194,A_195,B_196] :
      ( k2_xboole_0(k10_relat_1(C_194,A_195),k10_relat_1(C_194,B_196)) = k10_relat_1(C_194,k2_xboole_0(A_195,B_196))
      | ~ v1_relat_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1420,plain,(
    ! [A_195] :
      ( k2_xboole_0(k10_relat_1('#skF_5',A_195),k1_xboole_0) = k10_relat_1('#skF_5',k2_xboole_0(A_195,k1_xboole_0))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_1392])).

tff(c_1615,plain,(
    ! [A_205] : k2_xboole_0(k10_relat_1('#skF_5',A_205),k1_xboole_0) = k10_relat_1('#skF_5',k2_xboole_0(A_205,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1420])).

tff(c_1633,plain,
    ( k10_relat_1('#skF_5',k2_xboole_0(k9_relat_1('#skF_5',k1_relat_1('#skF_5')),k1_xboole_0)) = k2_xboole_0(k1_relat_1('#skF_5'),k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_1615])).

tff(c_1648,plain,(
    k10_relat_1('#skF_5',k2_xboole_0(k9_relat_1('#skF_5',k1_relat_1('#skF_5')),k1_xboole_0)) = k2_xboole_0(k1_relat_1('#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1633])).

tff(c_759,plain,(
    ! [B_156,A_157] :
      ( k9_relat_1(k2_funct_1(B_156),A_157) = k10_relat_1(B_156,A_157)
      | ~ v2_funct_1(B_156)
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2873,plain,(
    ! [B_266,A_267] :
      ( r1_tarski(k10_relat_1(B_266,A_267),k2_relat_1(k2_funct_1(B_266)))
      | ~ v1_relat_1(k2_funct_1(B_266))
      | ~ v2_funct_1(B_266)
      | ~ v1_funct_1(B_266)
      | ~ v1_relat_1(B_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_28])).

tff(c_2890,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1('#skF_5'),k1_xboole_0),k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1648,c_2873])).

tff(c_2923,plain,
    ( r1_tarski(k2_xboole_0(k1_relat_1('#skF_5'),k1_xboole_0),k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2890])).

tff(c_2932,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2923])).

tff(c_2935,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_2932])).

tff(c_2939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2935])).

tff(c_2941,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_2923])).

tff(c_46,plain,(
    ! [A_36] :
      ( v1_funct_1(k2_funct_1(A_36))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden('#skF_3'(A_25,B_26,C_27),k2_relat_1(C_27))
      | ~ r2_hidden(A_25,k10_relat_1(C_27,B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_567,plain,(
    ! [A_120,B_121,C_122] :
      ( r2_hidden('#skF_3'(A_120,B_121,C_122),B_121)
      | ~ r2_hidden(A_120,k10_relat_1(C_122,B_121))
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_275,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,B_81)
      | ~ r2_hidden(C_82,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_278,plain,(
    ! [C_82,A_19] :
      ( ~ r2_hidden(C_82,k1_xboole_0)
      | ~ r2_hidden(C_82,A_19) ) ),
    inference(resolution,[status(thm)],[c_26,c_275])).

tff(c_1277,plain,(
    ! [A_186,C_187,A_188] :
      ( ~ r2_hidden('#skF_3'(A_186,k1_xboole_0,C_187),A_188)
      | ~ r2_hidden(A_186,k10_relat_1(C_187,k1_xboole_0))
      | ~ v1_relat_1(C_187) ) ),
    inference(resolution,[status(thm)],[c_567,c_278])).

tff(c_1288,plain,(
    ! [A_189,C_190] :
      ( ~ r2_hidden(A_189,k10_relat_1(C_190,k1_xboole_0))
      | ~ v1_relat_1(C_190) ) ),
    inference(resolution,[status(thm)],[c_40,c_1277])).

tff(c_1446,plain,(
    ! [C_197,B_198] :
      ( ~ v1_relat_1(C_197)
      | r1_tarski(k10_relat_1(C_197,k1_xboole_0),B_198) ) ),
    inference(resolution,[status(thm)],[c_6,c_1288])).

tff(c_162,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_144])).

tff(c_1512,plain,(
    ! [C_197] :
      ( k10_relat_1(C_197,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_1446,c_162])).

tff(c_2950,plain,(
    k10_relat_1(k2_funct_1('#skF_5'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2941,c_1512])).

tff(c_940,plain,(
    ! [B_170] :
      ( k9_relat_1(B_170,k10_relat_1(B_170,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_24,c_929])).

tff(c_3029,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2950,c_940])).

tff(c_3111,plain,
    ( k9_relat_1(k2_funct_1('#skF_5'),k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_3029])).

tff(c_3152,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3111])).

tff(c_3188,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_3152])).

tff(c_3192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3188])).

tff(c_3194,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3111])).

tff(c_72,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,(
    ! [A_18] : k2_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(resolution,[status(thm)],[c_24,c_72])).

tff(c_54,plain,(
    ! [B_42,A_41] :
      ( k10_relat_1(k2_funct_1(B_42),A_41) = k9_relat_1(B_42,A_41)
      | ~ v2_funct_1(B_42)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_8584,plain,(
    ! [B_411,A_412,A_413] :
      ( k2_xboole_0(k10_relat_1(k2_funct_1(B_411),A_412),k9_relat_1(B_411,A_413)) = k10_relat_1(k2_funct_1(B_411),k2_xboole_0(A_412,A_413))
      | ~ v1_relat_1(k2_funct_1(B_411))
      | ~ v2_funct_1(B_411)
      | ~ v1_funct_1(B_411)
      | ~ v1_relat_1(B_411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1392])).

tff(c_8628,plain,(
    ! [A_413] :
      ( k10_relat_1(k2_funct_1('#skF_5'),k2_xboole_0(k1_xboole_0,A_413)) = k2_xboole_0(k1_xboole_0,k9_relat_1('#skF_5',A_413))
      | ~ v1_relat_1(k2_funct_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2950,c_8584])).

tff(c_8683,plain,(
    ! [A_413] : k10_relat_1(k2_funct_1('#skF_5'),A_413) = k9_relat_1('#skF_5',A_413) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2941,c_84,c_84,c_8628])).

tff(c_30,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_433,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,k10_relat_1(B_101,k9_relat_1(B_101,A_100)))
      | ~ r1_tarski(A_100,k1_relat_1(B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_449,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(A_22),k10_relat_1(A_22,k2_relat_1(A_22)))
      | ~ r1_tarski(k1_relat_1(A_22),k1_relat_1(A_22))
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_433])).

tff(c_456,plain,(
    ! [A_22] :
      ( r1_tarski(k1_relat_1(A_22),k10_relat_1(A_22,k2_relat_1(A_22)))
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_449])).

tff(c_871,plain,(
    ! [A_22] :
      ( k10_relat_1(A_22,k2_relat_1(A_22)) = k1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_456,c_853])).

tff(c_939,plain,(
    ! [B_170] :
      ( k9_relat_1(B_170,k10_relat_1(B_170,k2_relat_1(B_170))) = k2_relat_1(B_170)
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_18,c_929])).

tff(c_8689,plain,(
    ! [A_414] : k10_relat_1(k2_funct_1('#skF_5'),A_414) = k9_relat_1('#skF_5',A_414) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2941,c_84,c_84,c_8628])).

tff(c_8991,plain,(
    ! [A_414] :
      ( r1_tarski(k9_relat_1('#skF_5',A_414),k1_relat_1(k2_funct_1('#skF_5')))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8689,c_42])).

tff(c_9209,plain,(
    ! [A_415] : r1_tarski(k9_relat_1('#skF_5',A_415),k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_8991])).

tff(c_9235,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_9209])).

tff(c_9263,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_9235])).

tff(c_9020,plain,
    ( k9_relat_1('#skF_5',k2_relat_1(k2_funct_1('#skF_5'))) = k1_relat_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_8689])).

tff(c_9205,plain,(
    k9_relat_1('#skF_5',k2_relat_1(k2_funct_1('#skF_5'))) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_9020])).

tff(c_156,plain,(
    ! [B_21,A_20] :
      ( k9_relat_1(B_21,A_20) = k2_relat_1(B_21)
      | ~ r1_tarski(k2_relat_1(B_21),k9_relat_1(B_21,A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_9391,plain,
    ( k9_relat_1('#skF_5',k2_relat_1(k2_funct_1('#skF_5'))) = k2_relat_1('#skF_5')
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9205,c_156])).

tff(c_9434,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9263,c_9205,c_9391])).

tff(c_792,plain,(
    ! [B_156] :
      ( k10_relat_1(B_156,k1_relat_1(k2_funct_1(B_156))) = k2_relat_1(k2_funct_1(B_156))
      | ~ v2_funct_1(B_156)
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(k2_funct_1(B_156)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_759])).

tff(c_9482,plain,
    ( k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9434,c_792])).

tff(c_9541,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = k2_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_66,c_64,c_60,c_9482])).

tff(c_9836,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_9541])).

tff(c_9910,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9836])).

tff(c_52,plain,(
    ! [B_40,A_39] :
      ( k9_relat_1(B_40,k10_relat_1(B_40,A_39)) = A_39
      | ~ r1_tarski(A_39,k2_relat_1(B_40))
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9959,plain,(
    ! [A_39] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k10_relat_1(k2_funct_1('#skF_5'),A_39)) = A_39
      | ~ r1_tarski(A_39,k1_relat_1('#skF_5'))
      | ~ v1_funct_1(k2_funct_1('#skF_5'))
      | ~ v1_relat_1(k2_funct_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9910,c_52])).

tff(c_21567,plain,(
    ! [A_596] :
      ( k9_relat_1(k2_funct_1('#skF_5'),k9_relat_1('#skF_5',A_596)) = A_596
      | ~ r1_tarski(A_596,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2941,c_3194,c_8683,c_9959])).

tff(c_21701,plain,(
    ! [A_596] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_596)) = A_596
      | ~ r1_tarski(A_596,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_21567])).

tff(c_21969,plain,(
    ! [A_599] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_599)) = A_599
      | ~ r1_tarski(A_599,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_21701])).

tff(c_22045,plain,(
    k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_21969])).

tff(c_22083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_22045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.60/3.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.60/4.00  
% 10.60/4.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.60/4.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 10.60/4.00  
% 10.60/4.00  %Foreground sorts:
% 10.60/4.00  
% 10.60/4.00  
% 10.60/4.00  %Background operators:
% 10.60/4.00  
% 10.60/4.00  
% 10.60/4.00  %Foreground operators:
% 10.60/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.60/4.00  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.60/4.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.60/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.60/4.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.60/4.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.60/4.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.60/4.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.60/4.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.60/4.00  tff('#skF_5', type, '#skF_5': $i).
% 10.60/4.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.60/4.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.60/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.60/4.00  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.60/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.60/4.00  tff('#skF_4', type, '#skF_4': $i).
% 10.60/4.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.60/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.60/4.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.60/4.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.60/4.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.60/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.60/4.00  
% 10.60/4.02  tff(f_156, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 10.60/4.02  tff(f_145, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 10.60/4.02  tff(f_115, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.60/4.02  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.60/4.02  tff(f_121, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 10.60/4.02  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 10.60/4.02  tff(f_68, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.60/4.02  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 10.60/4.02  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 10.60/4.02  tff(f_107, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 10.60/4.02  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 10.60/4.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.60/4.02  tff(f_99, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 10.60/4.02  tff(f_70, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.60/4.02  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.60/4.02  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.60/4.02  tff(f_137, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 10.60/4.02  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 10.60/4.02  tff(c_58, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.60/4.02  tff(c_62, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.60/4.02  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.60/4.02  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.60/4.02  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.60/4.02  tff(c_56, plain, (![B_44, A_43]: (k9_relat_1(k2_funct_1(B_44), A_43)=k10_relat_1(B_44, A_43) | ~v2_funct_1(B_44) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.60/4.02  tff(c_48, plain, (![A_36]: (v1_relat_1(k2_funct_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.60/4.02  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.60/4.02  tff(c_50, plain, (![A_37, B_38]: (r1_tarski(A_37, k10_relat_1(B_38, k9_relat_1(B_38, A_37))) | ~r1_tarski(A_37, k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.60/4.02  tff(c_42, plain, (![B_32, A_31]: (r1_tarski(k10_relat_1(B_32, A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.60/4.02  tff(c_144, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.60/4.02  tff(c_853, plain, (![B_167, A_168]: (k10_relat_1(B_167, A_168)=k1_relat_1(B_167) | ~r1_tarski(k1_relat_1(B_167), k10_relat_1(B_167, A_168)) | ~v1_relat_1(B_167))), inference(resolution, [status(thm)], [c_42, c_144])).
% 10.60/4.02  tff(c_867, plain, (![B_38]: (k10_relat_1(B_38, k9_relat_1(B_38, k1_relat_1(B_38)))=k1_relat_1(B_38) | ~r1_tarski(k1_relat_1(B_38), k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_50, c_853])).
% 10.60/4.02  tff(c_874, plain, (![B_38]: (k10_relat_1(B_38, k9_relat_1(B_38, k1_relat_1(B_38)))=k1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_867])).
% 10.60/4.02  tff(c_24, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.60/4.02  tff(c_929, plain, (![B_170, A_171]: (k9_relat_1(B_170, k10_relat_1(B_170, A_171))=A_171 | ~r1_tarski(A_171, k2_relat_1(B_170)) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.60/4.02  tff(c_941, plain, (![B_172]: (k9_relat_1(B_172, k10_relat_1(B_172, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_172) | ~v1_relat_1(B_172))), inference(resolution, [status(thm)], [c_24, c_929])).
% 10.60/4.02  tff(c_311, plain, (![B_88, A_89]: (k9_relat_1(B_88, A_89)!=k1_xboole_0 | ~r1_tarski(A_89, k1_relat_1(B_88)) | k1_xboole_0=A_89 | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.60/4.02  tff(c_332, plain, (![B_32, A_31]: (k9_relat_1(B_32, k10_relat_1(B_32, A_31))!=k1_xboole_0 | k10_relat_1(B_32, A_31)=k1_xboole_0 | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_42, c_311])).
% 10.60/4.02  tff(c_988, plain, (![B_173]: (k10_relat_1(B_173, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(superposition, [status(thm), theory('equality')], [c_941, c_332])).
% 10.60/4.02  tff(c_994, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_988])).
% 10.60/4.02  tff(c_998, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_994])).
% 10.60/4.02  tff(c_1392, plain, (![C_194, A_195, B_196]: (k2_xboole_0(k10_relat_1(C_194, A_195), k10_relat_1(C_194, B_196))=k10_relat_1(C_194, k2_xboole_0(A_195, B_196)) | ~v1_relat_1(C_194))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.60/4.02  tff(c_1420, plain, (![A_195]: (k2_xboole_0(k10_relat_1('#skF_5', A_195), k1_xboole_0)=k10_relat_1('#skF_5', k2_xboole_0(A_195, k1_xboole_0)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_998, c_1392])).
% 10.60/4.02  tff(c_1615, plain, (![A_205]: (k2_xboole_0(k10_relat_1('#skF_5', A_205), k1_xboole_0)=k10_relat_1('#skF_5', k2_xboole_0(A_205, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1420])).
% 10.60/4.02  tff(c_1633, plain, (k10_relat_1('#skF_5', k2_xboole_0(k9_relat_1('#skF_5', k1_relat_1('#skF_5')), k1_xboole_0))=k2_xboole_0(k1_relat_1('#skF_5'), k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_874, c_1615])).
% 10.60/4.02  tff(c_1648, plain, (k10_relat_1('#skF_5', k2_xboole_0(k9_relat_1('#skF_5', k1_relat_1('#skF_5')), k1_xboole_0))=k2_xboole_0(k1_relat_1('#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1633])).
% 10.60/4.02  tff(c_759, plain, (![B_156, A_157]: (k9_relat_1(k2_funct_1(B_156), A_157)=k10_relat_1(B_156, A_157) | ~v2_funct_1(B_156) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.60/4.02  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.60/4.02  tff(c_2873, plain, (![B_266, A_267]: (r1_tarski(k10_relat_1(B_266, A_267), k2_relat_1(k2_funct_1(B_266))) | ~v1_relat_1(k2_funct_1(B_266)) | ~v2_funct_1(B_266) | ~v1_funct_1(B_266) | ~v1_relat_1(B_266))), inference(superposition, [status(thm), theory('equality')], [c_759, c_28])).
% 10.60/4.02  tff(c_2890, plain, (r1_tarski(k2_xboole_0(k1_relat_1('#skF_5'), k1_xboole_0), k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1648, c_2873])).
% 10.60/4.02  tff(c_2923, plain, (r1_tarski(k2_xboole_0(k1_relat_1('#skF_5'), k1_xboole_0), k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2890])).
% 10.60/4.02  tff(c_2932, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_2923])).
% 10.60/4.02  tff(c_2935, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_2932])).
% 10.60/4.02  tff(c_2939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2935])).
% 10.60/4.02  tff(c_2941, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_2923])).
% 10.60/4.02  tff(c_46, plain, (![A_36]: (v1_funct_1(k2_funct_1(A_36)) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.60/4.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.60/4.02  tff(c_40, plain, (![A_25, B_26, C_27]: (r2_hidden('#skF_3'(A_25, B_26, C_27), k2_relat_1(C_27)) | ~r2_hidden(A_25, k10_relat_1(C_27, B_26)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.60/4.02  tff(c_567, plain, (![A_120, B_121, C_122]: (r2_hidden('#skF_3'(A_120, B_121, C_122), B_121) | ~r2_hidden(A_120, k10_relat_1(C_122, B_121)) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.60/4.02  tff(c_26, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.60/4.02  tff(c_275, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, B_81) | ~r2_hidden(C_82, A_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.60/4.02  tff(c_278, plain, (![C_82, A_19]: (~r2_hidden(C_82, k1_xboole_0) | ~r2_hidden(C_82, A_19))), inference(resolution, [status(thm)], [c_26, c_275])).
% 10.60/4.02  tff(c_1277, plain, (![A_186, C_187, A_188]: (~r2_hidden('#skF_3'(A_186, k1_xboole_0, C_187), A_188) | ~r2_hidden(A_186, k10_relat_1(C_187, k1_xboole_0)) | ~v1_relat_1(C_187))), inference(resolution, [status(thm)], [c_567, c_278])).
% 10.60/4.02  tff(c_1288, plain, (![A_189, C_190]: (~r2_hidden(A_189, k10_relat_1(C_190, k1_xboole_0)) | ~v1_relat_1(C_190))), inference(resolution, [status(thm)], [c_40, c_1277])).
% 10.60/4.02  tff(c_1446, plain, (![C_197, B_198]: (~v1_relat_1(C_197) | r1_tarski(k10_relat_1(C_197, k1_xboole_0), B_198))), inference(resolution, [status(thm)], [c_6, c_1288])).
% 10.60/4.02  tff(c_162, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_144])).
% 10.60/4.02  tff(c_1512, plain, (![C_197]: (k10_relat_1(C_197, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_197))), inference(resolution, [status(thm)], [c_1446, c_162])).
% 10.60/4.02  tff(c_2950, plain, (k10_relat_1(k2_funct_1('#skF_5'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2941, c_1512])).
% 10.60/4.02  tff(c_940, plain, (![B_170]: (k9_relat_1(B_170, k10_relat_1(B_170, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_170) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_24, c_929])).
% 10.60/4.02  tff(c_3029, plain, (k9_relat_1(k2_funct_1('#skF_5'), k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2950, c_940])).
% 10.60/4.02  tff(c_3111, plain, (k9_relat_1(k2_funct_1('#skF_5'), k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_3029])).
% 10.60/4.02  tff(c_3152, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3111])).
% 10.60/4.02  tff(c_3188, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_3152])).
% 10.60/4.02  tff(c_3192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3188])).
% 10.60/4.02  tff(c_3194, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3111])).
% 10.60/4.02  tff(c_72, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.60/4.02  tff(c_84, plain, (![A_18]: (k2_xboole_0(k1_xboole_0, A_18)=A_18)), inference(resolution, [status(thm)], [c_24, c_72])).
% 10.60/4.02  tff(c_54, plain, (![B_42, A_41]: (k10_relat_1(k2_funct_1(B_42), A_41)=k9_relat_1(B_42, A_41) | ~v2_funct_1(B_42) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.60/4.02  tff(c_8584, plain, (![B_411, A_412, A_413]: (k2_xboole_0(k10_relat_1(k2_funct_1(B_411), A_412), k9_relat_1(B_411, A_413))=k10_relat_1(k2_funct_1(B_411), k2_xboole_0(A_412, A_413)) | ~v1_relat_1(k2_funct_1(B_411)) | ~v2_funct_1(B_411) | ~v1_funct_1(B_411) | ~v1_relat_1(B_411))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1392])).
% 10.60/4.02  tff(c_8628, plain, (![A_413]: (k10_relat_1(k2_funct_1('#skF_5'), k2_xboole_0(k1_xboole_0, A_413))=k2_xboole_0(k1_xboole_0, k9_relat_1('#skF_5', A_413)) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2950, c_8584])).
% 10.60/4.02  tff(c_8683, plain, (![A_413]: (k10_relat_1(k2_funct_1('#skF_5'), A_413)=k9_relat_1('#skF_5', A_413))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2941, c_84, c_84, c_8628])).
% 10.60/4.02  tff(c_30, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.60/4.02  tff(c_433, plain, (![A_100, B_101]: (r1_tarski(A_100, k10_relat_1(B_101, k9_relat_1(B_101, A_100))) | ~r1_tarski(A_100, k1_relat_1(B_101)) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.60/4.02  tff(c_449, plain, (![A_22]: (r1_tarski(k1_relat_1(A_22), k10_relat_1(A_22, k2_relat_1(A_22))) | ~r1_tarski(k1_relat_1(A_22), k1_relat_1(A_22)) | ~v1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_30, c_433])).
% 10.60/4.02  tff(c_456, plain, (![A_22]: (r1_tarski(k1_relat_1(A_22), k10_relat_1(A_22, k2_relat_1(A_22))) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_449])).
% 10.60/4.02  tff(c_871, plain, (![A_22]: (k10_relat_1(A_22, k2_relat_1(A_22))=k1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_456, c_853])).
% 10.60/4.02  tff(c_939, plain, (![B_170]: (k9_relat_1(B_170, k10_relat_1(B_170, k2_relat_1(B_170)))=k2_relat_1(B_170) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_18, c_929])).
% 10.60/4.02  tff(c_8689, plain, (![A_414]: (k10_relat_1(k2_funct_1('#skF_5'), A_414)=k9_relat_1('#skF_5', A_414))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2941, c_84, c_84, c_8628])).
% 10.60/4.02  tff(c_8991, plain, (![A_414]: (r1_tarski(k9_relat_1('#skF_5', A_414), k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8689, c_42])).
% 10.60/4.02  tff(c_9209, plain, (![A_415]: (r1_tarski(k9_relat_1('#skF_5', A_415), k1_relat_1(k2_funct_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_8991])).
% 10.60/4.02  tff(c_9235, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_939, c_9209])).
% 10.60/4.02  tff(c_9263, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_9235])).
% 10.60/4.02  tff(c_9020, plain, (k9_relat_1('#skF_5', k2_relat_1(k2_funct_1('#skF_5')))=k1_relat_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_871, c_8689])).
% 10.60/4.02  tff(c_9205, plain, (k9_relat_1('#skF_5', k2_relat_1(k2_funct_1('#skF_5')))=k1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_9020])).
% 10.60/4.02  tff(c_156, plain, (![B_21, A_20]: (k9_relat_1(B_21, A_20)=k2_relat_1(B_21) | ~r1_tarski(k2_relat_1(B_21), k9_relat_1(B_21, A_20)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_28, c_144])).
% 10.60/4.02  tff(c_9391, plain, (k9_relat_1('#skF_5', k2_relat_1(k2_funct_1('#skF_5')))=k2_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9205, c_156])).
% 10.60/4.02  tff(c_9434, plain, (k1_relat_1(k2_funct_1('#skF_5'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9263, c_9205, c_9391])).
% 10.60/4.02  tff(c_792, plain, (![B_156]: (k10_relat_1(B_156, k1_relat_1(k2_funct_1(B_156)))=k2_relat_1(k2_funct_1(B_156)) | ~v2_funct_1(B_156) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156) | ~v1_relat_1(k2_funct_1(B_156)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_759])).
% 10.60/4.02  tff(c_9482, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k2_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9434, c_792])).
% 10.60/4.02  tff(c_9541, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))=k2_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_66, c_64, c_60, c_9482])).
% 10.60/4.02  tff(c_9836, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_871, c_9541])).
% 10.60/4.02  tff(c_9910, plain, (k2_relat_1(k2_funct_1('#skF_5'))=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9836])).
% 10.60/4.02  tff(c_52, plain, (![B_40, A_39]: (k9_relat_1(B_40, k10_relat_1(B_40, A_39))=A_39 | ~r1_tarski(A_39, k2_relat_1(B_40)) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.60/4.02  tff(c_9959, plain, (![A_39]: (k9_relat_1(k2_funct_1('#skF_5'), k10_relat_1(k2_funct_1('#skF_5'), A_39))=A_39 | ~r1_tarski(A_39, k1_relat_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_9910, c_52])).
% 10.60/4.02  tff(c_21567, plain, (![A_596]: (k9_relat_1(k2_funct_1('#skF_5'), k9_relat_1('#skF_5', A_596))=A_596 | ~r1_tarski(A_596, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2941, c_3194, c_8683, c_9959])).
% 10.60/4.02  tff(c_21701, plain, (![A_596]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_596))=A_596 | ~r1_tarski(A_596, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_21567])).
% 10.60/4.02  tff(c_21969, plain, (![A_599]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_599))=A_599 | ~r1_tarski(A_599, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_21701])).
% 10.60/4.02  tff(c_22045, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_62, c_21969])).
% 10.60/4.02  tff(c_22083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_22045])).
% 10.60/4.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.60/4.02  
% 10.60/4.02  Inference rules
% 10.60/4.02  ----------------------
% 10.60/4.02  #Ref     : 0
% 10.60/4.02  #Sup     : 4882
% 10.60/4.02  #Fact    : 0
% 10.60/4.02  #Define  : 0
% 10.60/4.02  #Split   : 17
% 10.60/4.02  #Chain   : 0
% 10.60/4.02  #Close   : 0
% 10.60/4.02  
% 10.60/4.02  Ordering : KBO
% 10.60/4.02  
% 10.60/4.02  Simplification rules
% 10.60/4.02  ----------------------
% 10.60/4.02  #Subsume      : 1667
% 10.60/4.02  #Demod        : 5709
% 10.60/4.02  #Tautology    : 1583
% 10.60/4.02  #SimpNegUnit  : 96
% 10.60/4.02  #BackRed      : 32
% 10.60/4.02  
% 10.60/4.02  #Partial instantiations: 0
% 10.60/4.03  #Strategies tried      : 1
% 10.60/4.03  
% 10.60/4.03  Timing (in seconds)
% 10.60/4.03  ----------------------
% 10.60/4.03  Preprocessing        : 0.32
% 10.60/4.03  Parsing              : 0.18
% 10.60/4.03  CNF conversion       : 0.02
% 10.60/4.03  Main loop            : 2.92
% 10.60/4.03  Inferencing          : 0.77
% 10.60/4.03  Reduction            : 1.02
% 10.60/4.03  Demodulation         : 0.73
% 10.60/4.03  BG Simplification    : 0.07
% 10.60/4.03  Subsumption          : 0.87
% 10.60/4.03  Abstraction          : 0.11
% 10.60/4.03  MUC search           : 0.00
% 10.60/4.03  Cooper               : 0.00
% 10.60/4.03  Total                : 3.29
% 10.60/4.03  Index Insertion      : 0.00
% 10.60/4.03  Index Deletion       : 0.00
% 10.60/4.03  Index Matching       : 0.00
% 10.60/4.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
