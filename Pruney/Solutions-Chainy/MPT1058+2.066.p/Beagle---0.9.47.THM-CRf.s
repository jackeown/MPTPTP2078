%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 167 expanded)
%              Number of leaves         :   34 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :   97 ( 257 expanded)
%              Number of equality atoms :   38 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_93,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_27] : v1_funct_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_222,plain,(
    ! [B_73,A_74] : k5_relat_1(k6_relat_1(B_73),k6_relat_1(A_74)) = k6_relat_1(k3_xboole_0(A_74,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),B_25) = k7_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_74,B_73] :
      ( k7_relat_1(k6_relat_1(A_74),B_73) = k6_relat_1(k3_xboole_0(A_74,B_73))
      | ~ v1_relat_1(k6_relat_1(A_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_28])).

tff(c_271,plain,(
    ! [A_77,B_78] : k7_relat_1(k6_relat_1(A_77),B_78) = k6_relat_1(k3_xboole_0(A_77,B_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_228])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_277,plain,(
    ! [A_77,B_78] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_77,B_78))) = k9_relat_1(k6_relat_1(A_77),B_78)
      | ~ v1_relat_1(k6_relat_1(A_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_20])).

tff(c_298,plain,(
    ! [A_77,B_78] : k9_relat_1(k6_relat_1(A_77),B_78) = k3_xboole_0(A_77,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_277])).

tff(c_24,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    ! [A_47] :
      ( k7_relat_1(A_47,k1_relat_1(A_47)) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_83,plain,(
    ! [A_23] :
      ( k7_relat_1(k6_relat_1(A_23),A_23) = k6_relat_1(A_23)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_87,plain,(
    ! [A_23] : k7_relat_1(k6_relat_1(A_23),A_23) = k6_relat_1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_83])).

tff(c_150,plain,(
    ! [B_61,A_62] :
      ( k2_relat_1(k7_relat_1(B_61,A_62)) = k9_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_159,plain,(
    ! [A_23] :
      ( k9_relat_1(k6_relat_1(A_23),A_23) = k2_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_150])).

tff(c_166,plain,(
    ! [A_23] : k9_relat_1(k6_relat_1(A_23),A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_159])).

tff(c_1068,plain,(
    ! [A_145,B_146] :
      ( k3_xboole_0(A_145,k9_relat_1(B_146,k1_relat_1(B_146))) = k9_relat_1(B_146,k10_relat_1(B_146,A_145))
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1178,plain,(
    ! [A_23,A_145] :
      ( k9_relat_1(k6_relat_1(A_23),k10_relat_1(k6_relat_1(A_23),A_145)) = k3_xboole_0(A_145,k9_relat_1(k6_relat_1(A_23),A_23))
      | ~ v1_funct_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1068])).

tff(c_1185,plain,(
    ! [A_147,A_148] : k3_xboole_0(A_147,k10_relat_1(k6_relat_1(A_147),A_148)) = k3_xboole_0(A_148,A_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_298,c_166,c_1178])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1277,plain,(
    ! [A_148,A_147] : r1_tarski(k3_xboole_0(A_148,A_147),A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_1185,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_28,C_30,B_29] :
      ( k3_xboole_0(A_28,k10_relat_1(C_30,B_29)) = k10_relat_1(k7_relat_1(C_30,A_28),B_29)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1213,plain,(
    ! [A_147,A_148] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_147),A_147),A_148) = k3_xboole_0(A_148,A_147)
      | ~ v1_relat_1(k6_relat_1(A_147)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1185,c_36])).

tff(c_1287,plain,(
    ! [A_147,A_148] : k10_relat_1(k6_relat_1(A_147),A_148) = k3_xboole_0(A_148,A_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_87,c_1213])).

tff(c_1528,plain,(
    ! [A_163,C_164,B_165] :
      ( r1_tarski(A_163,k10_relat_1(C_164,B_165))
      | ~ r1_tarski(k9_relat_1(C_164,A_163),B_165)
      | ~ r1_tarski(A_163,k1_relat_1(C_164))
      | ~ v1_funct_1(C_164)
      | ~ v1_relat_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1537,plain,(
    ! [A_23,B_165] :
      ( r1_tarski(A_23,k10_relat_1(k6_relat_1(A_23),B_165))
      | ~ r1_tarski(A_23,B_165)
      | ~ r1_tarski(A_23,k1_relat_1(k6_relat_1(A_23)))
      | ~ v1_funct_1(k6_relat_1(A_23))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_1528])).

tff(c_1598,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(A_169,k3_xboole_0(B_170,A_169))
      | ~ r1_tarski(A_169,B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_6,c_24,c_1287,c_1537])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1621,plain,(
    ! [B_170,A_169] :
      ( k3_xboole_0(B_170,A_169) = A_169
      | ~ r1_tarski(k3_xboole_0(B_170,A_169),A_169)
      | ~ r1_tarski(A_169,B_170) ) ),
    inference(resolution,[status(thm)],[c_1598,c_2])).

tff(c_1644,plain,(
    ! [B_171,A_172] :
      ( k3_xboole_0(B_171,A_172) = A_172
      | ~ r1_tarski(A_172,B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_1621])).

tff(c_1711,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1644])).

tff(c_1981,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_36])).

tff(c_2015,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1981])).

tff(c_2017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.84  
% 3.97/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.85  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.97/1.85  
% 3.97/1.85  %Foreground sorts:
% 3.97/1.85  
% 3.97/1.85  
% 3.97/1.85  %Background operators:
% 3.97/1.85  
% 3.97/1.85  
% 3.97/1.85  %Foreground operators:
% 3.97/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.97/1.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.97/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.97/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.97/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.97/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.97/1.85  tff('#skF_2', type, '#skF_2': $i).
% 3.97/1.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.97/1.85  tff('#skF_3', type, '#skF_3': $i).
% 3.97/1.85  tff('#skF_1', type, '#skF_1': $i).
% 3.97/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.97/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.97/1.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.97/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.97/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.97/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.97/1.85  
% 3.97/1.86  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.97/1.86  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.97/1.86  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.97/1.86  tff(f_93, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.97/1.86  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.97/1.86  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.97/1.86  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 3.97/1.86  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 3.97/1.86  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.97/1.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.97/1.86  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.97/1.86  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.97/1.86  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.97/1.86  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.97/1.86  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.97/1.86  tff(c_32, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.97/1.86  tff(c_34, plain, (![A_27]: (v1_funct_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.97/1.86  tff(c_26, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.86  tff(c_222, plain, (![B_73, A_74]: (k5_relat_1(k6_relat_1(B_73), k6_relat_1(A_74))=k6_relat_1(k3_xboole_0(A_74, B_73)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.97/1.86  tff(c_28, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.86  tff(c_228, plain, (![A_74, B_73]: (k7_relat_1(k6_relat_1(A_74), B_73)=k6_relat_1(k3_xboole_0(A_74, B_73)) | ~v1_relat_1(k6_relat_1(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_222, c_28])).
% 3.97/1.86  tff(c_271, plain, (![A_77, B_78]: (k7_relat_1(k6_relat_1(A_77), B_78)=k6_relat_1(k3_xboole_0(A_77, B_78)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_228])).
% 3.97/1.86  tff(c_20, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.97/1.86  tff(c_277, plain, (![A_77, B_78]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_77, B_78)))=k9_relat_1(k6_relat_1(A_77), B_78) | ~v1_relat_1(k6_relat_1(A_77)))), inference(superposition, [status(thm), theory('equality')], [c_271, c_20])).
% 3.97/1.86  tff(c_298, plain, (![A_77, B_78]: (k9_relat_1(k6_relat_1(A_77), B_78)=k3_xboole_0(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_277])).
% 3.97/1.86  tff(c_24, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.86  tff(c_74, plain, (![A_47]: (k7_relat_1(A_47, k1_relat_1(A_47))=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.97/1.86  tff(c_83, plain, (![A_23]: (k7_relat_1(k6_relat_1(A_23), A_23)=k6_relat_1(A_23) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_74])).
% 3.97/1.86  tff(c_87, plain, (![A_23]: (k7_relat_1(k6_relat_1(A_23), A_23)=k6_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_83])).
% 3.97/1.86  tff(c_150, plain, (![B_61, A_62]: (k2_relat_1(k7_relat_1(B_61, A_62))=k9_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.97/1.86  tff(c_159, plain, (![A_23]: (k9_relat_1(k6_relat_1(A_23), A_23)=k2_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_150])).
% 3.97/1.86  tff(c_166, plain, (![A_23]: (k9_relat_1(k6_relat_1(A_23), A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_159])).
% 3.97/1.86  tff(c_1068, plain, (![A_145, B_146]: (k3_xboole_0(A_145, k9_relat_1(B_146, k1_relat_1(B_146)))=k9_relat_1(B_146, k10_relat_1(B_146, A_145)) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.97/1.86  tff(c_1178, plain, (![A_23, A_145]: (k9_relat_1(k6_relat_1(A_23), k10_relat_1(k6_relat_1(A_23), A_145))=k3_xboole_0(A_145, k9_relat_1(k6_relat_1(A_23), A_23)) | ~v1_funct_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1068])).
% 3.97/1.86  tff(c_1185, plain, (![A_147, A_148]: (k3_xboole_0(A_147, k10_relat_1(k6_relat_1(A_147), A_148))=k3_xboole_0(A_148, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_298, c_166, c_1178])).
% 3.97/1.86  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.97/1.86  tff(c_1277, plain, (![A_148, A_147]: (r1_tarski(k3_xboole_0(A_148, A_147), A_147))), inference(superposition, [status(thm), theory('equality')], [c_1185, c_8])).
% 3.97/1.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.86  tff(c_36, plain, (![A_28, C_30, B_29]: (k3_xboole_0(A_28, k10_relat_1(C_30, B_29))=k10_relat_1(k7_relat_1(C_30, A_28), B_29) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.97/1.86  tff(c_1213, plain, (![A_147, A_148]: (k10_relat_1(k7_relat_1(k6_relat_1(A_147), A_147), A_148)=k3_xboole_0(A_148, A_147) | ~v1_relat_1(k6_relat_1(A_147)))), inference(superposition, [status(thm), theory('equality')], [c_1185, c_36])).
% 3.97/1.86  tff(c_1287, plain, (![A_147, A_148]: (k10_relat_1(k6_relat_1(A_147), A_148)=k3_xboole_0(A_148, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_87, c_1213])).
% 3.97/1.86  tff(c_1528, plain, (![A_163, C_164, B_165]: (r1_tarski(A_163, k10_relat_1(C_164, B_165)) | ~r1_tarski(k9_relat_1(C_164, A_163), B_165) | ~r1_tarski(A_163, k1_relat_1(C_164)) | ~v1_funct_1(C_164) | ~v1_relat_1(C_164))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.97/1.86  tff(c_1537, plain, (![A_23, B_165]: (r1_tarski(A_23, k10_relat_1(k6_relat_1(A_23), B_165)) | ~r1_tarski(A_23, B_165) | ~r1_tarski(A_23, k1_relat_1(k6_relat_1(A_23))) | ~v1_funct_1(k6_relat_1(A_23)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_1528])).
% 3.97/1.86  tff(c_1598, plain, (![A_169, B_170]: (r1_tarski(A_169, k3_xboole_0(B_170, A_169)) | ~r1_tarski(A_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_6, c_24, c_1287, c_1537])).
% 3.97/1.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.86  tff(c_1621, plain, (![B_170, A_169]: (k3_xboole_0(B_170, A_169)=A_169 | ~r1_tarski(k3_xboole_0(B_170, A_169), A_169) | ~r1_tarski(A_169, B_170))), inference(resolution, [status(thm)], [c_1598, c_2])).
% 3.97/1.86  tff(c_1644, plain, (![B_171, A_172]: (k3_xboole_0(B_171, A_172)=A_172 | ~r1_tarski(A_172, B_171))), inference(demodulation, [status(thm), theory('equality')], [c_1277, c_1621])).
% 3.97/1.86  tff(c_1711, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1644])).
% 3.97/1.86  tff(c_1981, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1711, c_36])).
% 3.97/1.86  tff(c_2015, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1981])).
% 3.97/1.86  tff(c_2017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2015])).
% 3.97/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.86  
% 3.97/1.86  Inference rules
% 3.97/1.86  ----------------------
% 3.97/1.86  #Ref     : 0
% 3.97/1.86  #Sup     : 451
% 3.97/1.86  #Fact    : 0
% 3.97/1.86  #Define  : 0
% 3.97/1.86  #Split   : 1
% 3.97/1.86  #Chain   : 0
% 3.97/1.86  #Close   : 0
% 3.97/1.86  
% 3.97/1.86  Ordering : KBO
% 3.97/1.86  
% 3.97/1.86  Simplification rules
% 3.97/1.86  ----------------------
% 3.97/1.86  #Subsume      : 8
% 3.97/1.86  #Demod        : 211
% 3.97/1.86  #Tautology    : 161
% 3.97/1.86  #SimpNegUnit  : 1
% 3.97/1.86  #BackRed      : 14
% 3.97/1.86  
% 3.97/1.86  #Partial instantiations: 0
% 3.97/1.86  #Strategies tried      : 1
% 3.97/1.86  
% 3.97/1.86  Timing (in seconds)
% 3.97/1.86  ----------------------
% 3.97/1.86  Preprocessing        : 0.36
% 3.97/1.86  Parsing              : 0.19
% 3.97/1.86  CNF conversion       : 0.02
% 3.97/1.87  Main loop            : 0.60
% 3.97/1.87  Inferencing          : 0.20
% 3.97/1.87  Reduction            : 0.21
% 3.97/1.87  Demodulation         : 0.16
% 3.97/1.87  BG Simplification    : 0.03
% 3.97/1.87  Subsumption          : 0.12
% 3.97/1.87  Abstraction          : 0.03
% 3.97/1.87  MUC search           : 0.00
% 3.97/1.87  Cooper               : 0.00
% 3.97/1.87  Total                : 1.00
% 3.97/1.87  Index Insertion      : 0.00
% 3.97/1.87  Index Deletion       : 0.00
% 3.97/1.87  Index Matching       : 0.00
% 3.97/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
