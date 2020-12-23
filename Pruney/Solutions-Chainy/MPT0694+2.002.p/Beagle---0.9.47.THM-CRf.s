%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:53 EST 2020

% Result     : Theorem 27.37s
% Output     : CNFRefutation 27.37s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 161 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 252 expanded)
%              Number of equality atoms :   23 (  71 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_86583,plain,(
    ! [C_765,A_766,B_767] :
      ( r1_tarski(k9_relat_1(C_765,k3_xboole_0(A_766,B_767)),k3_xboole_0(k9_relat_1(C_765,A_766),k9_relat_1(C_765,B_767)))
      | ~ v1_relat_1(C_765) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k3_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86616,plain,(
    ! [C_765,A_766,B_767] :
      ( r1_tarski(k9_relat_1(C_765,k3_xboole_0(A_766,B_767)),k9_relat_1(C_765,A_766))
      | ~ v1_relat_1(C_765) ) ),
    inference(resolution,[status(thm)],[c_86583,c_10])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,k10_relat_1(B_21,A_20)),A_20)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [C_19,A_17,B_18] :
      ( r1_tarski(k9_relat_1(C_19,k3_xboole_0(A_17,B_18)),k3_xboole_0(k9_relat_1(C_19,A_17),k9_relat_1(C_19,B_18)))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_18,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_18])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_127,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k3_xboole_0(B_9,C_10))
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_387,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,k3_xboole_0(A_62,B_63)) ) ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_391,plain,(
    ! [B_9,C_10] :
      ( k3_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_387])).

tff(c_401,plain,(
    ! [B_64,C_65] :
      ( k3_xboole_0(B_64,C_65) = B_64
      | ~ r1_tarski(B_64,C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_391])).

tff(c_644,plain,(
    ! [B_72,A_73] : k3_xboole_0(k3_xboole_0(B_72,A_73),A_73) = k3_xboole_0(B_72,A_73) ),
    inference(resolution,[status(thm)],[c_127,c_401])).

tff(c_95,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_18])).

tff(c_704,plain,(
    ! [A_73,B_72] : k3_xboole_0(A_73,k3_xboole_0(B_72,A_73)) = k3_xboole_0(B_72,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_95])).

tff(c_176,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(A_39,B_40)
      | ~ r1_tarski(A_39,k3_xboole_0(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [B_40,C_41,B_4] : r1_tarski(k3_xboole_0(k3_xboole_0(B_40,C_41),B_4),B_40) ),
    inference(resolution,[status(thm)],[c_8,c_176])).

tff(c_312,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1939,plain,(
    ! [B_100,C_101,A_102] :
      ( k3_xboole_0(B_100,C_101) = A_102
      | ~ r1_tarski(k3_xboole_0(B_100,C_101),A_102)
      | ~ r1_tarski(A_102,C_101)
      | ~ r1_tarski(A_102,B_100) ) ),
    inference(resolution,[status(thm)],[c_312,c_2])).

tff(c_3780,plain,(
    ! [B_148,C_149,B_150] :
      ( k3_xboole_0(k3_xboole_0(B_148,C_149),B_150) = B_148
      | ~ r1_tarski(B_148,B_150)
      | ~ r1_tarski(B_148,k3_xboole_0(B_148,C_149)) ) ),
    inference(resolution,[status(thm)],[c_196,c_1939])).

tff(c_3801,plain,(
    ! [B_9,C_10,B_150] :
      ( k3_xboole_0(k3_xboole_0(B_9,C_10),B_150) = B_9
      | ~ r1_tarski(B_9,B_150)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_3780])).

tff(c_8476,plain,(
    ! [B_219,C_220,B_221] :
      ( k3_xboole_0(k3_xboole_0(B_219,C_220),B_221) = B_219
      | ~ r1_tarski(B_219,B_221)
      | ~ r1_tarski(B_219,C_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3801])).

tff(c_199,plain,(
    ! [B_42,C_43,B_44] : r1_tarski(k3_xboole_0(k3_xboole_0(B_42,C_43),B_44),B_42) ),
    inference(resolution,[status(thm)],[c_8,c_176])).

tff(c_208,plain,(
    ! [B_31,A_32,B_44] : r1_tarski(k3_xboole_0(k3_xboole_0(B_31,A_32),B_44),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_199])).

tff(c_18619,plain,(
    ! [B_293,B_294,B_295,C_296] :
      ( r1_tarski(k3_xboole_0(B_293,B_294),B_295)
      | ~ r1_tarski(B_293,B_295)
      | ~ r1_tarski(B_293,C_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8476,c_208])).

tff(c_18734,plain,(
    ! [B_297,B_298,B_299] :
      ( r1_tarski(k3_xboole_0(B_297,B_298),B_299)
      | ~ r1_tarski(B_297,B_299) ) ),
    inference(resolution,[status(thm)],[c_6,c_18619])).

tff(c_19127,plain,(
    ! [B_304,A_305,B_306] :
      ( r1_tarski(k3_xboole_0(B_304,A_305),B_306)
      | ~ r1_tarski(A_305,B_306) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_18734])).

tff(c_1991,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(B_33,A_34) = A_34
      | ~ r1_tarski(A_34,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(resolution,[status(thm)],[c_127,c_1939])).

tff(c_2025,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(B_33,A_34) = A_34
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1991])).

tff(c_68417,plain,(
    ! [B_674,B_675,A_676] :
      ( k3_xboole_0(B_674,k3_xboole_0(B_675,A_676)) = k3_xboole_0(B_675,A_676)
      | ~ r1_tarski(A_676,B_674) ) ),
    inference(resolution,[status(thm)],[c_19127,c_2025])).

tff(c_70189,plain,(
    ! [A_677,B_678,B_679,A_680] :
      ( r1_tarski(A_677,B_678)
      | ~ r1_tarski(A_677,k3_xboole_0(B_679,A_680))
      | ~ r1_tarski(A_680,B_678) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68417,c_10])).

tff(c_86053,plain,(
    ! [C_756,A_757,B_758,B_759] :
      ( r1_tarski(k9_relat_1(C_756,k3_xboole_0(A_757,B_758)),B_759)
      | ~ r1_tarski(k9_relat_1(C_756,B_758),B_759)
      | ~ v1_relat_1(C_756) ) ),
    inference(resolution,[status(thm)],[c_20,c_70189])).

tff(c_24,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_24])).

tff(c_329,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_312,c_151])).

tff(c_386,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_86237,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86053,c_386])).

tff(c_86446,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_86237])).

tff(c_86457,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_86446])).

tff(c_86461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_86457])).

tff(c_86462,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_87201,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86616,c_86462])).

tff(c_87205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_87201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.37/17.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.37/17.59  
% 27.37/17.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.37/17.59  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 27.37/17.59  
% 27.37/17.59  %Foreground sorts:
% 27.37/17.59  
% 27.37/17.59  
% 27.37/17.59  %Background operators:
% 27.37/17.59  
% 27.37/17.59  
% 27.37/17.59  %Foreground operators:
% 27.37/17.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.37/17.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.37/17.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.37/17.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.37/17.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 27.37/17.59  tff('#skF_2', type, '#skF_2': $i).
% 27.37/17.59  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.37/17.59  tff('#skF_3', type, '#skF_3': $i).
% 27.37/17.59  tff('#skF_1', type, '#skF_1': $i).
% 27.37/17.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.37/17.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 27.37/17.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.37/17.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.37/17.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.37/17.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.37/17.59  
% 27.37/17.61  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 27.37/17.61  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 27.37/17.61  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 27.37/17.61  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 27.37/17.61  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 27.37/17.61  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 27.37/17.61  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 27.37/17.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.37/17.61  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 27.37/17.61  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.37/17.61  tff(c_86583, plain, (![C_765, A_766, B_767]: (r1_tarski(k9_relat_1(C_765, k3_xboole_0(A_766, B_767)), k3_xboole_0(k9_relat_1(C_765, A_766), k9_relat_1(C_765, B_767))) | ~v1_relat_1(C_765))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.37/17.61  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k3_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.37/17.61  tff(c_86616, plain, (![C_765, A_766, B_767]: (r1_tarski(k9_relat_1(C_765, k3_xboole_0(A_766, B_767)), k9_relat_1(C_765, A_766)) | ~v1_relat_1(C_765))), inference(resolution, [status(thm)], [c_86583, c_10])).
% 27.37/17.61  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.37/17.61  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, k10_relat_1(B_21, A_20)), A_20) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.37/17.61  tff(c_20, plain, (![C_19, A_17, B_18]: (r1_tarski(k9_relat_1(C_19, k3_xboole_0(A_17, B_18)), k3_xboole_0(k9_relat_1(C_19, A_17), k9_relat_1(C_19, B_18))) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.37/17.61  tff(c_14, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.37/17.61  tff(c_65, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.37/17.61  tff(c_89, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_14, c_65])).
% 27.37/17.61  tff(c_18, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.37/17.61  tff(c_112, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_89, c_18])).
% 27.37/17.61  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.37/17.61  tff(c_127, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_112, c_8])).
% 27.37/17.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.37/17.61  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k3_xboole_0(B_9, C_10)) | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.37/17.61  tff(c_163, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.37/17.61  tff(c_387, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, k3_xboole_0(A_62, B_63)))), inference(resolution, [status(thm)], [c_8, c_163])).
% 27.37/17.61  tff(c_391, plain, (![B_9, C_10]: (k3_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(B_9, C_10) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_387])).
% 27.37/17.61  tff(c_401, plain, (![B_64, C_65]: (k3_xboole_0(B_64, C_65)=B_64 | ~r1_tarski(B_64, C_65))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_391])).
% 27.37/17.61  tff(c_644, plain, (![B_72, A_73]: (k3_xboole_0(k3_xboole_0(B_72, A_73), A_73)=k3_xboole_0(B_72, A_73))), inference(resolution, [status(thm)], [c_127, c_401])).
% 27.37/17.61  tff(c_95, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_89, c_18])).
% 27.37/17.61  tff(c_704, plain, (![A_73, B_72]: (k3_xboole_0(A_73, k3_xboole_0(B_72, A_73))=k3_xboole_0(B_72, A_73))), inference(superposition, [status(thm), theory('equality')], [c_644, c_95])).
% 27.37/17.61  tff(c_176, plain, (![A_39, B_40, C_41]: (r1_tarski(A_39, B_40) | ~r1_tarski(A_39, k3_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.37/17.61  tff(c_196, plain, (![B_40, C_41, B_4]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_40, C_41), B_4), B_40))), inference(resolution, [status(thm)], [c_8, c_176])).
% 27.37/17.61  tff(c_312, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 27.37/17.61  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.37/17.61  tff(c_1939, plain, (![B_100, C_101, A_102]: (k3_xboole_0(B_100, C_101)=A_102 | ~r1_tarski(k3_xboole_0(B_100, C_101), A_102) | ~r1_tarski(A_102, C_101) | ~r1_tarski(A_102, B_100))), inference(resolution, [status(thm)], [c_312, c_2])).
% 27.37/17.61  tff(c_3780, plain, (![B_148, C_149, B_150]: (k3_xboole_0(k3_xboole_0(B_148, C_149), B_150)=B_148 | ~r1_tarski(B_148, B_150) | ~r1_tarski(B_148, k3_xboole_0(B_148, C_149)))), inference(resolution, [status(thm)], [c_196, c_1939])).
% 27.37/17.61  tff(c_3801, plain, (![B_9, C_10, B_150]: (k3_xboole_0(k3_xboole_0(B_9, C_10), B_150)=B_9 | ~r1_tarski(B_9, B_150) | ~r1_tarski(B_9, C_10) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_3780])).
% 27.37/17.61  tff(c_8476, plain, (![B_219, C_220, B_221]: (k3_xboole_0(k3_xboole_0(B_219, C_220), B_221)=B_219 | ~r1_tarski(B_219, B_221) | ~r1_tarski(B_219, C_220))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3801])).
% 27.37/17.61  tff(c_199, plain, (![B_42, C_43, B_44]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_42, C_43), B_44), B_42))), inference(resolution, [status(thm)], [c_8, c_176])).
% 27.37/17.61  tff(c_208, plain, (![B_31, A_32, B_44]: (r1_tarski(k3_xboole_0(k3_xboole_0(B_31, A_32), B_44), A_32))), inference(superposition, [status(thm), theory('equality')], [c_95, c_199])).
% 27.37/17.61  tff(c_18619, plain, (![B_293, B_294, B_295, C_296]: (r1_tarski(k3_xboole_0(B_293, B_294), B_295) | ~r1_tarski(B_293, B_295) | ~r1_tarski(B_293, C_296))), inference(superposition, [status(thm), theory('equality')], [c_8476, c_208])).
% 27.37/17.61  tff(c_18734, plain, (![B_297, B_298, B_299]: (r1_tarski(k3_xboole_0(B_297, B_298), B_299) | ~r1_tarski(B_297, B_299))), inference(resolution, [status(thm)], [c_6, c_18619])).
% 27.37/17.61  tff(c_19127, plain, (![B_304, A_305, B_306]: (r1_tarski(k3_xboole_0(B_304, A_305), B_306) | ~r1_tarski(A_305, B_306))), inference(superposition, [status(thm), theory('equality')], [c_704, c_18734])).
% 27.37/17.61  tff(c_1991, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=A_34 | ~r1_tarski(A_34, A_34) | ~r1_tarski(A_34, B_33))), inference(resolution, [status(thm)], [c_127, c_1939])).
% 27.37/17.61  tff(c_2025, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=A_34 | ~r1_tarski(A_34, B_33))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1991])).
% 27.37/17.61  tff(c_68417, plain, (![B_674, B_675, A_676]: (k3_xboole_0(B_674, k3_xboole_0(B_675, A_676))=k3_xboole_0(B_675, A_676) | ~r1_tarski(A_676, B_674))), inference(resolution, [status(thm)], [c_19127, c_2025])).
% 27.37/17.61  tff(c_70189, plain, (![A_677, B_678, B_679, A_680]: (r1_tarski(A_677, B_678) | ~r1_tarski(A_677, k3_xboole_0(B_679, A_680)) | ~r1_tarski(A_680, B_678))), inference(superposition, [status(thm), theory('equality')], [c_68417, c_10])).
% 27.37/17.61  tff(c_86053, plain, (![C_756, A_757, B_758, B_759]: (r1_tarski(k9_relat_1(C_756, k3_xboole_0(A_757, B_758)), B_759) | ~r1_tarski(k9_relat_1(C_756, B_758), B_759) | ~v1_relat_1(C_756))), inference(resolution, [status(thm)], [c_20, c_70189])).
% 27.37/17.61  tff(c_24, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.37/17.61  tff(c_151, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_24])).
% 27.37/17.61  tff(c_329, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_312, c_151])).
% 27.37/17.61  tff(c_386, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_329])).
% 27.37/17.61  tff(c_86237, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86053, c_386])).
% 27.37/17.61  tff(c_86446, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_86237])).
% 27.37/17.61  tff(c_86457, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_86446])).
% 27.37/17.61  tff(c_86461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_86457])).
% 27.37/17.61  tff(c_86462, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_329])).
% 27.37/17.61  tff(c_87201, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86616, c_86462])).
% 27.37/17.61  tff(c_87205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_87201])).
% 27.37/17.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.37/17.61  
% 27.37/17.61  Inference rules
% 27.37/17.61  ----------------------
% 27.37/17.61  #Ref     : 0
% 27.37/17.61  #Sup     : 22509
% 27.37/17.61  #Fact    : 0
% 27.37/17.61  #Define  : 0
% 27.37/17.61  #Split   : 2
% 27.37/17.61  #Chain   : 0
% 27.37/17.61  #Close   : 0
% 27.37/17.61  
% 27.37/17.61  Ordering : KBO
% 27.37/17.61  
% 27.37/17.61  Simplification rules
% 27.37/17.61  ----------------------
% 27.37/17.61  #Subsume      : 3186
% 27.37/17.61  #Demod        : 11569
% 27.37/17.61  #Tautology    : 7321
% 27.37/17.61  #SimpNegUnit  : 0
% 27.37/17.61  #BackRed      : 0
% 27.37/17.61  
% 27.37/17.61  #Partial instantiations: 0
% 27.37/17.61  #Strategies tried      : 1
% 27.37/17.61  
% 27.37/17.61  Timing (in seconds)
% 27.37/17.61  ----------------------
% 27.37/17.61  Preprocessing        : 0.31
% 27.37/17.61  Parsing              : 0.16
% 27.37/17.61  CNF conversion       : 0.02
% 27.37/17.61  Main loop            : 16.53
% 27.37/17.61  Inferencing          : 1.75
% 27.37/17.61  Reduction            : 9.62
% 27.37/17.61  Demodulation         : 9.06
% 27.37/17.61  BG Simplification    : 0.28
% 27.37/17.61  Subsumption          : 4.19
% 27.37/17.61  Abstraction          : 0.40
% 27.37/17.61  MUC search           : 0.00
% 27.37/17.61  Cooper               : 0.00
% 27.37/17.61  Total                : 16.88
% 27.37/17.61  Index Insertion      : 0.00
% 27.37/17.61  Index Deletion       : 0.00
% 27.37/17.61  Index Matching       : 0.00
% 27.37/17.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
