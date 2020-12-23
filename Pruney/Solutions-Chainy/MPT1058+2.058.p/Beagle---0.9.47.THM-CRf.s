%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:29 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 230 expanded)
%              Number of leaves         :   31 (  99 expanded)
%              Depth                    :   17
%              Number of atoms          :  124 ( 422 expanded)
%              Number of equality atoms :   29 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
          & r1_tarski(A,k2_relat_1(C)) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_38,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_22,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,k10_relat_1(B_21,k9_relat_1(B_21,A_20)))
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [A_14] : v1_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    ! [A_41] :
      ( k10_relat_1(A_41,k2_relat_1(A_41)) = k1_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [A_13] :
      ( k10_relat_1(k6_relat_1(A_13),A_13) = k1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_98,plain,(
    ! [A_13] : k10_relat_1(k6_relat_1(A_13),A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_94])).

tff(c_1259,plain,(
    ! [A_117,B_118,C_119] :
      ( r1_tarski(A_117,B_118)
      | ~ r1_tarski(A_117,k2_relat_1(C_119))
      | ~ r1_tarski(k10_relat_1(C_119,A_117),k10_relat_1(C_119,B_118))
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1284,plain,(
    ! [A_13,B_118] :
      ( r1_tarski(A_13,B_118)
      | ~ r1_tarski(A_13,k2_relat_1(k6_relat_1(A_13)))
      | ~ r1_tarski(A_13,k10_relat_1(k6_relat_1(A_13),B_118))
      | ~ v1_funct_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_1259])).

tff(c_1311,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(A_120,B_121)
      | ~ r1_tarski(A_120,k10_relat_1(k6_relat_1(A_120),B_121)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_6,c_20,c_1284])).

tff(c_1318,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,k9_relat_1(k6_relat_1(A_20),A_20))
      | ~ r1_tarski(A_20,k1_relat_1(k6_relat_1(A_20)))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1311])).

tff(c_1330,plain,(
    ! [A_20] : r1_tarski(A_20,k9_relat_1(k6_relat_1(A_20),A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_18,c_1318])).

tff(c_253,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k9_relat_1(B_60,k10_relat_1(B_60,A_61)),A_61)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_268,plain,(
    ! [A_13] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_13),A_13),A_13)
      | ~ v1_funct_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_253])).

tff(c_278,plain,(
    ! [A_62] : r1_tarski(k9_relat_1(k6_relat_1(A_62),A_62),A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_268])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_294,plain,(
    ! [A_62] :
      ( k9_relat_1(k6_relat_1(A_62),A_62) = A_62
      | ~ r1_tarski(A_62,k9_relat_1(k6_relat_1(A_62),A_62)) ) ),
    inference(resolution,[status(thm)],[c_278,c_2])).

tff(c_1336,plain,(
    ! [A_62] : k9_relat_1(k6_relat_1(A_62),A_62) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_294])).

tff(c_1536,plain,(
    ! [A_131,C_132,B_133] :
      ( r1_tarski(A_131,k10_relat_1(C_132,B_133))
      | ~ r1_tarski(k9_relat_1(C_132,A_131),B_133)
      | ~ r1_tarski(A_131,k1_relat_1(C_132))
      | ~ v1_funct_1(C_132)
      | ~ v1_relat_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1539,plain,(
    ! [A_62,B_133] :
      ( r1_tarski(A_62,k10_relat_1(k6_relat_1(A_62),B_133))
      | ~ r1_tarski(A_62,B_133)
      | ~ r1_tarski(A_62,k1_relat_1(k6_relat_1(A_62)))
      | ~ v1_funct_1(k6_relat_1(A_62))
      | ~ v1_relat_1(k6_relat_1(A_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_1536])).

tff(c_1812,plain,(
    ! [A_148,B_149] :
      ( r1_tarski(A_148,k10_relat_1(k6_relat_1(A_148),B_149))
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_6,c_18,c_1539])).

tff(c_108,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k10_relat_1(B_43,A_44),k1_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [A_13,A_44] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_13),A_44),A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_108])).

tff(c_122,plain,(
    ! [A_13,A_44] : r1_tarski(k10_relat_1(k6_relat_1(A_13),A_44),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_134,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [A_13,A_44] :
      ( k10_relat_1(k6_relat_1(A_13),A_44) = A_13
      | ~ r1_tarski(A_13,k10_relat_1(k6_relat_1(A_13),A_44)) ) ),
    inference(resolution,[status(thm)],[c_122,c_134])).

tff(c_1854,plain,(
    ! [A_148,B_149] :
      ( k10_relat_1(k6_relat_1(A_148),B_149) = A_148
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(resolution,[status(thm)],[c_1812,c_143])).

tff(c_968,plain,(
    ! [A_102,B_103] :
      ( k3_xboole_0(A_102,k9_relat_1(B_103,k1_relat_1(B_103))) = k9_relat_1(B_103,k10_relat_1(B_103,A_102))
      | ~ v1_funct_1(B_103)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_977,plain,(
    ! [A_13,A_102] :
      ( k9_relat_1(k6_relat_1(A_13),k10_relat_1(k6_relat_1(A_13),A_102)) = k3_xboole_0(A_102,k9_relat_1(k6_relat_1(A_13),A_13))
      | ~ v1_funct_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_968])).

tff(c_981,plain,(
    ! [A_13,A_102] : k9_relat_1(k6_relat_1(A_13),k10_relat_1(k6_relat_1(A_13),A_102)) = k3_xboole_0(A_102,k9_relat_1(k6_relat_1(A_13),A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_977])).

tff(c_2370,plain,(
    ! [A_163,A_164] : k9_relat_1(k6_relat_1(A_163),k10_relat_1(k6_relat_1(A_163),A_164)) = k3_xboole_0(A_164,A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_981])).

tff(c_2396,plain,(
    ! [A_148,B_149] :
      ( k9_relat_1(k6_relat_1(A_148),A_148) = k3_xboole_0(B_149,A_148)
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1854,c_2370])).

tff(c_2420,plain,(
    ! [B_165,A_166] :
      ( k3_xboole_0(B_165,A_166) = A_166
      | ~ r1_tarski(A_166,B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_2396])).

tff(c_2511,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2420])).

tff(c_26,plain,(
    ! [A_15,C_17,B_16] :
      ( k3_xboole_0(A_15,k10_relat_1(C_17,B_16)) = k10_relat_1(k7_relat_1(C_17,A_15),B_16)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2670,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2511,c_26])).

tff(c_2683,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2670])).

tff(c_2685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.66  
% 4.00/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.66  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.00/1.66  
% 4.00/1.66  %Foreground sorts:
% 4.00/1.66  
% 4.00/1.66  
% 4.00/1.66  %Background operators:
% 4.00/1.66  
% 4.00/1.66  
% 4.00/1.66  %Foreground operators:
% 4.00/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.00/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.00/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.00/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.00/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.00/1.66  tff('#skF_2', type, '#skF_2': $i).
% 4.00/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.00/1.66  tff('#skF_3', type, '#skF_3': $i).
% 4.00/1.66  tff('#skF_1', type, '#skF_1': $i).
% 4.00/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.00/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.00/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.00/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.00/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.00/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.00/1.66  
% 4.12/1.68  tff(f_109, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 4.12/1.68  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.12/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.12/1.68  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.12/1.68  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.12/1.68  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.12/1.68  tff(f_89, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 4.12/1.68  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 4.12/1.68  tff(f_99, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 4.12/1.68  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 4.12/1.68  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 4.12/1.68  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 4.12/1.68  tff(c_38, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.12/1.68  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.12/1.68  tff(c_40, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.12/1.68  tff(c_22, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.68  tff(c_18, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.68  tff(c_30, plain, (![A_20, B_21]: (r1_tarski(A_20, k10_relat_1(B_21, k9_relat_1(B_21, A_20))) | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.12/1.68  tff(c_24, plain, (![A_14]: (v1_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.68  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.68  tff(c_85, plain, (![A_41]: (k10_relat_1(A_41, k2_relat_1(A_41))=k1_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.68  tff(c_94, plain, (![A_13]: (k10_relat_1(k6_relat_1(A_13), A_13)=k1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_85])).
% 4.12/1.68  tff(c_98, plain, (![A_13]: (k10_relat_1(k6_relat_1(A_13), A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_94])).
% 4.12/1.68  tff(c_1259, plain, (![A_117, B_118, C_119]: (r1_tarski(A_117, B_118) | ~r1_tarski(A_117, k2_relat_1(C_119)) | ~r1_tarski(k10_relat_1(C_119, A_117), k10_relat_1(C_119, B_118)) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.12/1.68  tff(c_1284, plain, (![A_13, B_118]: (r1_tarski(A_13, B_118) | ~r1_tarski(A_13, k2_relat_1(k6_relat_1(A_13))) | ~r1_tarski(A_13, k10_relat_1(k6_relat_1(A_13), B_118)) | ~v1_funct_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_1259])).
% 4.12/1.68  tff(c_1311, plain, (![A_120, B_121]: (r1_tarski(A_120, B_121) | ~r1_tarski(A_120, k10_relat_1(k6_relat_1(A_120), B_121)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_6, c_20, c_1284])).
% 4.12/1.68  tff(c_1318, plain, (![A_20]: (r1_tarski(A_20, k9_relat_1(k6_relat_1(A_20), A_20)) | ~r1_tarski(A_20, k1_relat_1(k6_relat_1(A_20))) | ~v1_relat_1(k6_relat_1(A_20)))), inference(resolution, [status(thm)], [c_30, c_1311])).
% 4.12/1.68  tff(c_1330, plain, (![A_20]: (r1_tarski(A_20, k9_relat_1(k6_relat_1(A_20), A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_18, c_1318])).
% 4.12/1.68  tff(c_253, plain, (![B_60, A_61]: (r1_tarski(k9_relat_1(B_60, k10_relat_1(B_60, A_61)), A_61) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.12/1.68  tff(c_268, plain, (![A_13]: (r1_tarski(k9_relat_1(k6_relat_1(A_13), A_13), A_13) | ~v1_funct_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_253])).
% 4.12/1.68  tff(c_278, plain, (![A_62]: (r1_tarski(k9_relat_1(k6_relat_1(A_62), A_62), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_268])).
% 4.12/1.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.68  tff(c_294, plain, (![A_62]: (k9_relat_1(k6_relat_1(A_62), A_62)=A_62 | ~r1_tarski(A_62, k9_relat_1(k6_relat_1(A_62), A_62)))), inference(resolution, [status(thm)], [c_278, c_2])).
% 4.12/1.68  tff(c_1336, plain, (![A_62]: (k9_relat_1(k6_relat_1(A_62), A_62)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_294])).
% 4.12/1.68  tff(c_1536, plain, (![A_131, C_132, B_133]: (r1_tarski(A_131, k10_relat_1(C_132, B_133)) | ~r1_tarski(k9_relat_1(C_132, A_131), B_133) | ~r1_tarski(A_131, k1_relat_1(C_132)) | ~v1_funct_1(C_132) | ~v1_relat_1(C_132))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.12/1.68  tff(c_1539, plain, (![A_62, B_133]: (r1_tarski(A_62, k10_relat_1(k6_relat_1(A_62), B_133)) | ~r1_tarski(A_62, B_133) | ~r1_tarski(A_62, k1_relat_1(k6_relat_1(A_62))) | ~v1_funct_1(k6_relat_1(A_62)) | ~v1_relat_1(k6_relat_1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_1336, c_1536])).
% 4.12/1.68  tff(c_1812, plain, (![A_148, B_149]: (r1_tarski(A_148, k10_relat_1(k6_relat_1(A_148), B_149)) | ~r1_tarski(A_148, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_6, c_18, c_1539])).
% 4.12/1.68  tff(c_108, plain, (![B_43, A_44]: (r1_tarski(k10_relat_1(B_43, A_44), k1_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.12/1.68  tff(c_117, plain, (![A_13, A_44]: (r1_tarski(k10_relat_1(k6_relat_1(A_13), A_44), A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_108])).
% 4.12/1.68  tff(c_122, plain, (![A_13, A_44]: (r1_tarski(k10_relat_1(k6_relat_1(A_13), A_44), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_117])).
% 4.12/1.68  tff(c_134, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.68  tff(c_143, plain, (![A_13, A_44]: (k10_relat_1(k6_relat_1(A_13), A_44)=A_13 | ~r1_tarski(A_13, k10_relat_1(k6_relat_1(A_13), A_44)))), inference(resolution, [status(thm)], [c_122, c_134])).
% 4.12/1.68  tff(c_1854, plain, (![A_148, B_149]: (k10_relat_1(k6_relat_1(A_148), B_149)=A_148 | ~r1_tarski(A_148, B_149))), inference(resolution, [status(thm)], [c_1812, c_143])).
% 4.12/1.68  tff(c_968, plain, (![A_102, B_103]: (k3_xboole_0(A_102, k9_relat_1(B_103, k1_relat_1(B_103)))=k9_relat_1(B_103, k10_relat_1(B_103, A_102)) | ~v1_funct_1(B_103) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.12/1.68  tff(c_977, plain, (![A_13, A_102]: (k9_relat_1(k6_relat_1(A_13), k10_relat_1(k6_relat_1(A_13), A_102))=k3_xboole_0(A_102, k9_relat_1(k6_relat_1(A_13), A_13)) | ~v1_funct_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_968])).
% 4.12/1.68  tff(c_981, plain, (![A_13, A_102]: (k9_relat_1(k6_relat_1(A_13), k10_relat_1(k6_relat_1(A_13), A_102))=k3_xboole_0(A_102, k9_relat_1(k6_relat_1(A_13), A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_977])).
% 4.12/1.68  tff(c_2370, plain, (![A_163, A_164]: (k9_relat_1(k6_relat_1(A_163), k10_relat_1(k6_relat_1(A_163), A_164))=k3_xboole_0(A_164, A_163))), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_981])).
% 4.12/1.68  tff(c_2396, plain, (![A_148, B_149]: (k9_relat_1(k6_relat_1(A_148), A_148)=k3_xboole_0(B_149, A_148) | ~r1_tarski(A_148, B_149))), inference(superposition, [status(thm), theory('equality')], [c_1854, c_2370])).
% 4.12/1.68  tff(c_2420, plain, (![B_165, A_166]: (k3_xboole_0(B_165, A_166)=A_166 | ~r1_tarski(A_166, B_165))), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_2396])).
% 4.12/1.68  tff(c_2511, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_2420])).
% 4.12/1.68  tff(c_26, plain, (![A_15, C_17, B_16]: (k3_xboole_0(A_15, k10_relat_1(C_17, B_16))=k10_relat_1(k7_relat_1(C_17, A_15), B_16) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.12/1.68  tff(c_2670, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2511, c_26])).
% 4.12/1.68  tff(c_2683, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2670])).
% 4.12/1.68  tff(c_2685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2683])).
% 4.12/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.68  
% 4.12/1.68  Inference rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Ref     : 0
% 4.12/1.68  #Sup     : 565
% 4.12/1.68  #Fact    : 0
% 4.12/1.68  #Define  : 0
% 4.12/1.68  #Split   : 1
% 4.12/1.68  #Chain   : 0
% 4.12/1.68  #Close   : 0
% 4.12/1.68  
% 4.12/1.68  Ordering : KBO
% 4.12/1.68  
% 4.12/1.68  Simplification rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Subsume      : 43
% 4.12/1.68  #Demod        : 517
% 4.12/1.68  #Tautology    : 254
% 4.12/1.68  #SimpNegUnit  : 1
% 4.12/1.68  #BackRed      : 15
% 4.12/1.68  
% 4.12/1.68  #Partial instantiations: 0
% 4.12/1.68  #Strategies tried      : 1
% 4.12/1.68  
% 4.12/1.68  Timing (in seconds)
% 4.12/1.68  ----------------------
% 4.12/1.68  Preprocessing        : 0.32
% 4.12/1.68  Parsing              : 0.17
% 4.12/1.68  CNF conversion       : 0.02
% 4.12/1.68  Main loop            : 0.60
% 4.12/1.68  Inferencing          : 0.20
% 4.12/1.68  Reduction            : 0.22
% 4.12/1.68  Demodulation         : 0.17
% 4.12/1.68  BG Simplification    : 0.03
% 4.12/1.68  Subsumption          : 0.11
% 4.12/1.68  Abstraction          : 0.04
% 4.12/1.68  MUC search           : 0.00
% 4.12/1.68  Cooper               : 0.00
% 4.12/1.68  Total                : 0.95
% 4.12/1.68  Index Insertion      : 0.00
% 4.12/1.68  Index Deletion       : 0.00
% 4.12/1.68  Index Matching       : 0.00
% 4.12/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
