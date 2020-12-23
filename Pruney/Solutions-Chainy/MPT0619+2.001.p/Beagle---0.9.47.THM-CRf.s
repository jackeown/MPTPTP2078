%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:51 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 320 expanded)
%              Number of leaves         :   38 ( 130 expanded)
%              Depth                    :   16
%              Number of atoms          :  140 ( 739 expanded)
%              Number of equality atoms :   53 ( 281 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_2'(A_25,B_26),A_25)
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_209,plain,(
    ! [B_79,A_80] :
      ( k7_relat_1(B_79,A_80) = B_79
      | ~ r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_220,plain,(
    ! [B_83] :
      ( k7_relat_1(B_83,k1_relat_1(B_83)) = B_83
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_12,c_209])).

tff(c_36,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(k7_relat_1(B_32,A_31)) = k9_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_232,plain,(
    ! [B_84] :
      ( k9_relat_1(B_84,k1_relat_1(B_84)) = k2_relat_1(B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_36])).

tff(c_52,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_138,plain,(
    ! [A_62,B_63] :
      ( k9_relat_1(A_62,k1_tarski(B_63)) = k11_relat_1(A_62,B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_147,plain,(
    ! [A_62] :
      ( k9_relat_1(A_62,k1_relat_1('#skF_4')) = k11_relat_1(A_62,'#skF_3')
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_138])).

tff(c_239,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_147])).

tff(c_249,plain,(
    k11_relat_1('#skF_4','#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_56,c_239])).

tff(c_38,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_645,plain,(
    ! [C_126,A_127,B_128] :
      ( k1_funct_1(C_126,A_127) = B_128
      | ~ r2_hidden(k4_tarski(A_127,B_128),C_126)
      | ~ v1_funct_1(C_126)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_733,plain,(
    ! [C_134,A_135,B_136] :
      ( k1_funct_1(C_134,A_135) = B_136
      | ~ v1_funct_1(C_134)
      | ~ r2_hidden(B_136,k11_relat_1(C_134,A_135))
      | ~ v1_relat_1(C_134) ) ),
    inference(resolution,[status(thm)],[c_38,c_645])).

tff(c_744,plain,(
    ! [B_136] :
      ( k1_funct_1('#skF_4','#skF_3') = B_136
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(B_136,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_733])).

tff(c_775,plain,(
    ! [B_139] :
      ( k1_funct_1('#skF_4','#skF_3') = B_139
      | ~ r2_hidden(B_139,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_744])).

tff(c_794,plain,(
    ! [B_26] :
      ( '#skF_2'(k2_relat_1('#skF_4'),B_26) = k1_funct_1('#skF_4','#skF_3')
      | k2_relat_1('#skF_4') = k1_xboole_0
      | k2_relat_1('#skF_4') = k1_tarski(B_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_775])).

tff(c_1854,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_794])).

tff(c_14,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [A_50,C_51,B_52] :
      ( r2_hidden(A_50,C_51)
      | ~ r1_tarski(k2_tarski(A_50,B_52),C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    ! [A_53,B_54] : r2_hidden(A_53,k2_tarski(A_53,B_54)) ),
    inference(resolution,[status(thm)],[c_12,c_94])).

tff(c_126,plain,(
    ! [A_61] : r2_hidden(A_61,k1_tarski(A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_103])).

tff(c_132,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_126])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_795,plain,
    ( '#skF_1'(k2_relat_1('#skF_4')) = k1_funct_1('#skF_4','#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_775])).

tff(c_1075,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_795])).

tff(c_204,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),A_77)
      | k1_xboole_0 = A_77
      | k1_tarski(B_78) = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [A_77,B_78] :
      ( ~ v1_xboole_0(A_77)
      | k1_xboole_0 = A_77
      | k1_tarski(B_78) = A_77 ) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_1078,plain,(
    ! [B_78] :
      ( k2_relat_1('#skF_4') = k1_xboole_0
      | k2_relat_1('#skF_4') = k1_tarski(B_78) ) ),
    inference(resolution,[status(thm)],[c_1075,c_208])).

tff(c_1079,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1078])).

tff(c_1085,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_249])).

tff(c_665,plain,(
    ! [A_129,C_130] :
      ( r2_hidden(k4_tarski(A_129,k1_funct_1(C_130,A_129)),C_130)
      | ~ r2_hidden(A_129,k1_relat_1(C_130))
      | ~ v1_funct_1(C_130)
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    ! [B_34,C_35,A_33] :
      ( r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1261,plain,(
    ! [C_155,A_156] :
      ( r2_hidden(k1_funct_1(C_155,A_156),k11_relat_1(C_155,A_156))
      | ~ r2_hidden(A_156,k1_relat_1(C_155))
      | ~ v1_funct_1(C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_665,c_40])).

tff(c_1275,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_3'),k1_xboole_0)
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_1261])).

tff(c_1282,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_132,c_1275])).

tff(c_1288,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1282,c_2])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1288])).

tff(c_1295,plain,(
    ! [B_78] : k2_relat_1('#skF_4') = k1_tarski(B_78) ),
    inference(splitRight,[status(thm)],[c_1078])).

tff(c_50,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_50])).

tff(c_1303,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_795])).

tff(c_1859,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_1303])).

tff(c_1868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1859])).

tff(c_1870,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_794])).

tff(c_1871,plain,(
    ! [B_189] :
      ( '#skF_2'(k2_relat_1('#skF_4'),B_189) = k1_funct_1('#skF_4','#skF_3')
      | k2_relat_1('#skF_4') = k1_tarski(B_189) ) ),
    inference(splitRight,[status(thm)],[c_794])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( '#skF_2'(A_25,B_26) != B_26
      | k1_xboole_0 = A_25
      | k1_tarski(B_26) = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1879,plain,(
    ! [B_189] :
      ( k1_funct_1('#skF_4','#skF_3') != B_189
      | k2_relat_1('#skF_4') = k1_xboole_0
      | k2_relat_1('#skF_4') = k1_tarski(B_189)
      | k2_relat_1('#skF_4') = k1_tarski(B_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_30])).

tff(c_1888,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k2_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1870,c_1879])).

tff(c_1891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.62  
% 3.76/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.63  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.76/1.63  
% 3.76/1.63  %Foreground sorts:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Background operators:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Foreground operators:
% 3.76/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.76/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.76/1.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.76/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.76/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.76/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.76/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.76/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.76/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.76/1.63  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.76/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.76/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.76/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.76/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.76/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.76/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.76/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.76/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.76/1.63  
% 3.76/1.64  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.76/1.64  tff(f_68, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.76/1.64  tff(f_108, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.76/1.64  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.76/1.64  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.76/1.64  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.76/1.64  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.76/1.64  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 3.76/1.64  tff(f_99, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.76/1.64  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.76/1.64  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.76/1.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.76/1.64  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.76/1.64  tff(c_32, plain, (![A_25, B_26]: (r2_hidden('#skF_2'(A_25, B_26), A_25) | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.76/1.64  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.76/1.64  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.76/1.64  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.76/1.64  tff(c_209, plain, (![B_79, A_80]: (k7_relat_1(B_79, A_80)=B_79 | ~r1_tarski(k1_relat_1(B_79), A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.76/1.64  tff(c_220, plain, (![B_83]: (k7_relat_1(B_83, k1_relat_1(B_83))=B_83 | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_12, c_209])).
% 3.76/1.64  tff(c_36, plain, (![B_32, A_31]: (k2_relat_1(k7_relat_1(B_32, A_31))=k9_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.76/1.64  tff(c_232, plain, (![B_84]: (k9_relat_1(B_84, k1_relat_1(B_84))=k2_relat_1(B_84) | ~v1_relat_1(B_84) | ~v1_relat_1(B_84))), inference(superposition, [status(thm), theory('equality')], [c_220, c_36])).
% 3.76/1.64  tff(c_52, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.76/1.64  tff(c_138, plain, (![A_62, B_63]: (k9_relat_1(A_62, k1_tarski(B_63))=k11_relat_1(A_62, B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.76/1.64  tff(c_147, plain, (![A_62]: (k9_relat_1(A_62, k1_relat_1('#skF_4'))=k11_relat_1(A_62, '#skF_3') | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_52, c_138])).
% 3.76/1.64  tff(c_239, plain, (k11_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_232, c_147])).
% 3.76/1.64  tff(c_249, plain, (k11_relat_1('#skF_4', '#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_56, c_239])).
% 3.76/1.64  tff(c_38, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_33, B_34), C_35) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.76/1.64  tff(c_645, plain, (![C_126, A_127, B_128]: (k1_funct_1(C_126, A_127)=B_128 | ~r2_hidden(k4_tarski(A_127, B_128), C_126) | ~v1_funct_1(C_126) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.76/1.64  tff(c_733, plain, (![C_134, A_135, B_136]: (k1_funct_1(C_134, A_135)=B_136 | ~v1_funct_1(C_134) | ~r2_hidden(B_136, k11_relat_1(C_134, A_135)) | ~v1_relat_1(C_134))), inference(resolution, [status(thm)], [c_38, c_645])).
% 3.76/1.64  tff(c_744, plain, (![B_136]: (k1_funct_1('#skF_4', '#skF_3')=B_136 | ~v1_funct_1('#skF_4') | ~r2_hidden(B_136, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_249, c_733])).
% 3.76/1.64  tff(c_775, plain, (![B_139]: (k1_funct_1('#skF_4', '#skF_3')=B_139 | ~r2_hidden(B_139, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_744])).
% 3.76/1.64  tff(c_794, plain, (![B_26]: ('#skF_2'(k2_relat_1('#skF_4'), B_26)=k1_funct_1('#skF_4', '#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')=k1_tarski(B_26))), inference(resolution, [status(thm)], [c_32, c_775])).
% 3.76/1.64  tff(c_1854, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_794])).
% 3.76/1.64  tff(c_14, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.76/1.64  tff(c_94, plain, (![A_50, C_51, B_52]: (r2_hidden(A_50, C_51) | ~r1_tarski(k2_tarski(A_50, B_52), C_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.76/1.64  tff(c_103, plain, (![A_53, B_54]: (r2_hidden(A_53, k2_tarski(A_53, B_54)))), inference(resolution, [status(thm)], [c_12, c_94])).
% 3.76/1.64  tff(c_126, plain, (![A_61]: (r2_hidden(A_61, k1_tarski(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_103])).
% 3.76/1.64  tff(c_132, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_126])).
% 3.76/1.64  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.64  tff(c_795, plain, ('#skF_1'(k2_relat_1('#skF_4'))=k1_funct_1('#skF_4', '#skF_3') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_775])).
% 3.76/1.64  tff(c_1075, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_795])).
% 3.76/1.64  tff(c_204, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), A_77) | k1_xboole_0=A_77 | k1_tarski(B_78)=A_77)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.76/1.64  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.64  tff(c_208, plain, (![A_77, B_78]: (~v1_xboole_0(A_77) | k1_xboole_0=A_77 | k1_tarski(B_78)=A_77)), inference(resolution, [status(thm)], [c_204, c_2])).
% 3.76/1.64  tff(c_1078, plain, (![B_78]: (k2_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')=k1_tarski(B_78))), inference(resolution, [status(thm)], [c_1075, c_208])).
% 3.76/1.64  tff(c_1079, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1078])).
% 3.76/1.64  tff(c_1085, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_249])).
% 3.76/1.64  tff(c_665, plain, (![A_129, C_130]: (r2_hidden(k4_tarski(A_129, k1_funct_1(C_130, A_129)), C_130) | ~r2_hidden(A_129, k1_relat_1(C_130)) | ~v1_funct_1(C_130) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.76/1.64  tff(c_40, plain, (![B_34, C_35, A_33]: (r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~r2_hidden(k4_tarski(A_33, B_34), C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.76/1.64  tff(c_1261, plain, (![C_155, A_156]: (r2_hidden(k1_funct_1(C_155, A_156), k11_relat_1(C_155, A_156)) | ~r2_hidden(A_156, k1_relat_1(C_155)) | ~v1_funct_1(C_155) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_665, c_40])).
% 3.76/1.64  tff(c_1275, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k1_xboole_0) | ~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1085, c_1261])).
% 3.76/1.64  tff(c_1282, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_132, c_1275])).
% 3.76/1.64  tff(c_1288, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1282, c_2])).
% 3.76/1.64  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1288])).
% 3.76/1.64  tff(c_1295, plain, (![B_78]: (k2_relat_1('#skF_4')=k1_tarski(B_78))), inference(splitRight, [status(thm)], [c_1078])).
% 3.76/1.64  tff(c_50, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.76/1.64  tff(c_1301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1295, c_50])).
% 3.76/1.64  tff(c_1303, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_795])).
% 3.76/1.64  tff(c_1859, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_1303])).
% 3.76/1.64  tff(c_1868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1859])).
% 3.76/1.64  tff(c_1870, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_794])).
% 3.76/1.64  tff(c_1871, plain, (![B_189]: ('#skF_2'(k2_relat_1('#skF_4'), B_189)=k1_funct_1('#skF_4', '#skF_3') | k2_relat_1('#skF_4')=k1_tarski(B_189))), inference(splitRight, [status(thm)], [c_794])).
% 3.76/1.64  tff(c_30, plain, (![A_25, B_26]: ('#skF_2'(A_25, B_26)!=B_26 | k1_xboole_0=A_25 | k1_tarski(B_26)=A_25)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.76/1.64  tff(c_1879, plain, (![B_189]: (k1_funct_1('#skF_4', '#skF_3')!=B_189 | k2_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')=k1_tarski(B_189) | k2_relat_1('#skF_4')=k1_tarski(B_189))), inference(superposition, [status(thm), theory('equality')], [c_1871, c_30])).
% 3.76/1.64  tff(c_1888, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1870, c_1879])).
% 3.76/1.64  tff(c_1891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1888, c_50])).
% 3.76/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.64  
% 3.76/1.64  Inference rules
% 3.76/1.64  ----------------------
% 3.76/1.64  #Ref     : 0
% 3.76/1.64  #Sup     : 388
% 3.76/1.64  #Fact    : 0
% 3.76/1.64  #Define  : 0
% 3.76/1.64  #Split   : 9
% 3.76/1.64  #Chain   : 0
% 3.76/1.64  #Close   : 0
% 3.76/1.64  
% 3.76/1.64  Ordering : KBO
% 3.76/1.64  
% 3.76/1.64  Simplification rules
% 3.76/1.64  ----------------------
% 3.76/1.64  #Subsume      : 67
% 3.76/1.64  #Demod        : 267
% 3.76/1.64  #Tautology    : 162
% 3.76/1.64  #SimpNegUnit  : 18
% 3.76/1.64  #BackRed      : 49
% 3.76/1.64  
% 3.76/1.64  #Partial instantiations: 0
% 3.76/1.64  #Strategies tried      : 1
% 3.76/1.64  
% 3.76/1.64  Timing (in seconds)
% 3.76/1.64  ----------------------
% 3.76/1.64  Preprocessing        : 0.34
% 3.76/1.64  Parsing              : 0.18
% 3.76/1.64  CNF conversion       : 0.02
% 3.76/1.64  Main loop            : 0.54
% 3.76/1.64  Inferencing          : 0.19
% 3.76/1.65  Reduction            : 0.18
% 3.76/1.65  Demodulation         : 0.13
% 3.76/1.65  BG Simplification    : 0.03
% 3.76/1.65  Subsumption          : 0.10
% 3.76/1.65  Abstraction          : 0.03
% 3.76/1.65  MUC search           : 0.00
% 3.76/1.65  Cooper               : 0.00
% 3.76/1.65  Total                : 0.92
% 3.76/1.65  Index Insertion      : 0.00
% 3.76/1.65  Index Deletion       : 0.00
% 3.76/1.65  Index Matching       : 0.00
% 3.76/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
