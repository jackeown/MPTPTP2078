%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:27 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :   77 (  91 expanded)
%              Number of leaves         :   37 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 150 expanded)
%              Number of equality atoms :   31 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_101,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(k2_relat_1(B),k1_relat_1(C))
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(k5_relat_1(B,C),k9_relat_1(C,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k10_relat_1(B_26,k9_relat_1(B_26,A_25)),A_25)
      | ~ v2_funct_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_335,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_65,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_335])).

tff(c_207,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_xboole_0(A_55,k4_xboole_0(C_56,B_57))
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1159,plain,(
    ! [C_116,B_117] :
      ( k4_xboole_0(C_116,B_117) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_116,B_117),B_117) ) ),
    inference(resolution,[status(thm)],[c_207,c_18])).

tff(c_1350,plain,(
    ! [C_122] :
      ( k4_xboole_0(C_122,k1_relat_1('#skF_2')) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_122,k1_relat_1('#skF_2')),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_346,c_1159])).

tff(c_1389,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1350])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1417,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_14])).

tff(c_1433,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1417])).

tff(c_34,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_22] : k1_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [B_32,A_31] : k5_relat_1(k6_relat_1(B_32),k6_relat_1(A_31)) = k6_relat_1(k3_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_443,plain,(
    ! [A_73,B_74] :
      ( k10_relat_1(A_73,k1_relat_1(B_74)) = k1_relat_1(k5_relat_1(A_73,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_452,plain,(
    ! [A_73,A_22] :
      ( k1_relat_1(k5_relat_1(A_73,k6_relat_1(A_22))) = k10_relat_1(A_73,A_22)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_443])).

tff(c_4217,plain,(
    ! [A_186,A_187] :
      ( k1_relat_1(k5_relat_1(A_186,k6_relat_1(A_187))) = k10_relat_1(A_186,A_187)
      | ~ v1_relat_1(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_452])).

tff(c_4232,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_31,B_32))) = k10_relat_1(k6_relat_1(B_32),A_31)
      | ~ v1_relat_1(k6_relat_1(B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4217])).

tff(c_4243,plain,(
    ! [B_32,A_31] : k10_relat_1(k6_relat_1(B_32),A_31) = k3_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_4232])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_23)),A_23) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_972,plain,(
    ! [B_107,A_108,C_109] :
      ( r1_tarski(k10_relat_1(B_107,A_108),k10_relat_1(k5_relat_1(B_107,C_109),k9_relat_1(C_109,A_108)))
      | ~ r1_tarski(k2_relat_1(B_107),k1_relat_1(C_109))
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_990,plain,(
    ! [A_23,A_108] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_23)),A_108),k10_relat_1(A_23,k9_relat_1(A_23,A_108)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_23))),k1_relat_1(A_23))
      | ~ v1_relat_1(A_23)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_23)))
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_972])).

tff(c_999,plain,(
    ! [A_23,A_108] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_23)),A_108),k10_relat_1(A_23,k9_relat_1(A_23,A_108)))
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6,c_30,c_990])).

tff(c_5047,plain,(
    ! [A_205,A_206] :
      ( r1_tarski(k3_xboole_0(A_205,k1_relat_1(A_206)),k10_relat_1(A_206,k9_relat_1(A_206,A_205)))
      | ~ v1_relat_1(A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4243,c_999])).

tff(c_5077,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_5047])).

tff(c_5099,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5077])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5108,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5099,c_2])).

tff(c_5114,plain,(
    ~ r1_tarski(k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5108])).

tff(c_5117,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_5114])).

tff(c_5121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_5117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.81  
% 4.42/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.81  %$ r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.42/1.81  
% 4.42/1.81  %Foreground sorts:
% 4.42/1.81  
% 4.42/1.81  
% 4.42/1.81  %Background operators:
% 4.42/1.81  
% 4.42/1.81  
% 4.42/1.81  %Foreground operators:
% 4.42/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.42/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.42/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.42/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.42/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.42/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.42/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.42/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.42/1.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.42/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.42/1.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.42/1.81  
% 4.42/1.82  tff(f_112, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 4.42/1.82  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 4.42/1.82  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.42/1.82  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.42/1.82  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.42/1.82  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.42/1.82  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.42/1.82  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.42/1.82  tff(f_82, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.42/1.82  tff(f_74, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.42/1.82  tff(f_101, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.42/1.82  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 4.42/1.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.42/1.82  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 4.42/1.82  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(C)) => r1_tarski(k10_relat_1(B, A), k10_relat_1(k5_relat_1(B, C), k9_relat_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_funct_1)).
% 4.42/1.82  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.42/1.82  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.42/1.82  tff(c_46, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.42/1.82  tff(c_38, plain, (![B_26, A_25]: (r1_tarski(k10_relat_1(B_26, k9_relat_1(B_26, A_25)), A_25) | ~v2_funct_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.42/1.82  tff(c_44, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.42/1.82  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.42/1.82  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.82  tff(c_48, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.42/1.82  tff(c_335, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.42/1.82  tff(c_346, plain, (![A_65]: (r1_tarski(A_65, k1_relat_1('#skF_2')) | ~r1_tarski(A_65, '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_335])).
% 4.42/1.82  tff(c_207, plain, (![A_55, C_56, B_57]: (r1_xboole_0(A_55, k4_xboole_0(C_56, B_57)) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.42/1.82  tff(c_18, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.42/1.82  tff(c_1159, plain, (![C_116, B_117]: (k4_xboole_0(C_116, B_117)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_116, B_117), B_117))), inference(resolution, [status(thm)], [c_207, c_18])).
% 4.42/1.82  tff(c_1350, plain, (![C_122]: (k4_xboole_0(C_122, k1_relat_1('#skF_2'))=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_122, k1_relat_1('#skF_2')), '#skF_1'))), inference(resolution, [status(thm)], [c_346, c_1159])).
% 4.42/1.82  tff(c_1389, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1350])).
% 4.42/1.82  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.82  tff(c_1417, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1389, c_14])).
% 4.42/1.82  tff(c_1433, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1417])).
% 4.42/1.82  tff(c_34, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.42/1.82  tff(c_28, plain, (![A_22]: (k1_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.42/1.82  tff(c_42, plain, (![B_32, A_31]: (k5_relat_1(k6_relat_1(B_32), k6_relat_1(A_31))=k6_relat_1(k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.42/1.82  tff(c_443, plain, (![A_73, B_74]: (k10_relat_1(A_73, k1_relat_1(B_74))=k1_relat_1(k5_relat_1(A_73, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.42/1.82  tff(c_452, plain, (![A_73, A_22]: (k1_relat_1(k5_relat_1(A_73, k6_relat_1(A_22)))=k10_relat_1(A_73, A_22) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_28, c_443])).
% 4.42/1.82  tff(c_4217, plain, (![A_186, A_187]: (k1_relat_1(k5_relat_1(A_186, k6_relat_1(A_187)))=k10_relat_1(A_186, A_187) | ~v1_relat_1(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_452])).
% 4.42/1.82  tff(c_4232, plain, (![A_31, B_32]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_31, B_32)))=k10_relat_1(k6_relat_1(B_32), A_31) | ~v1_relat_1(k6_relat_1(B_32)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4217])).
% 4.42/1.82  tff(c_4243, plain, (![B_32, A_31]: (k10_relat_1(k6_relat_1(B_32), A_31)=k3_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_4232])).
% 4.42/1.82  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.42/1.82  tff(c_30, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.42/1.82  tff(c_32, plain, (![A_23]: (k5_relat_1(k6_relat_1(k1_relat_1(A_23)), A_23)=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.42/1.82  tff(c_972, plain, (![B_107, A_108, C_109]: (r1_tarski(k10_relat_1(B_107, A_108), k10_relat_1(k5_relat_1(B_107, C_109), k9_relat_1(C_109, A_108))) | ~r1_tarski(k2_relat_1(B_107), k1_relat_1(C_109)) | ~v1_relat_1(C_109) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.42/1.82  tff(c_990, plain, (![A_23, A_108]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_23)), A_108), k10_relat_1(A_23, k9_relat_1(A_23, A_108))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_23))), k1_relat_1(A_23)) | ~v1_relat_1(A_23) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_23))) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_32, c_972])).
% 4.42/1.82  tff(c_999, plain, (![A_23, A_108]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_23)), A_108), k10_relat_1(A_23, k9_relat_1(A_23, A_108))) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6, c_30, c_990])).
% 4.42/1.82  tff(c_5047, plain, (![A_205, A_206]: (r1_tarski(k3_xboole_0(A_205, k1_relat_1(A_206)), k10_relat_1(A_206, k9_relat_1(A_206, A_205))) | ~v1_relat_1(A_206))), inference(demodulation, [status(thm), theory('equality')], [c_4243, c_999])).
% 4.42/1.82  tff(c_5077, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1433, c_5047])).
% 4.42/1.82  tff(c_5099, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_5077])).
% 4.42/1.82  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.42/1.82  tff(c_5108, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(resolution, [status(thm)], [c_5099, c_2])).
% 4.42/1.82  tff(c_5114, plain, (~r1_tarski(k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_5108])).
% 4.42/1.82  tff(c_5117, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_5114])).
% 4.42/1.82  tff(c_5121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_5117])).
% 4.42/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.82  
% 4.42/1.82  Inference rules
% 4.42/1.82  ----------------------
% 4.42/1.82  #Ref     : 0
% 4.42/1.82  #Sup     : 1171
% 4.42/1.82  #Fact    : 0
% 4.42/1.82  #Define  : 0
% 4.42/1.82  #Split   : 1
% 4.42/1.82  #Chain   : 0
% 4.42/1.82  #Close   : 0
% 4.42/1.82  
% 4.42/1.82  Ordering : KBO
% 4.42/1.82  
% 4.42/1.82  Simplification rules
% 4.42/1.82  ----------------------
% 4.42/1.82  #Subsume      : 72
% 4.42/1.82  #Demod        : 1332
% 4.42/1.82  #Tautology    : 893
% 4.42/1.82  #SimpNegUnit  : 1
% 4.42/1.82  #BackRed      : 3
% 4.42/1.82  
% 4.42/1.82  #Partial instantiations: 0
% 4.42/1.83  #Strategies tried      : 1
% 4.42/1.83  
% 4.42/1.83  Timing (in seconds)
% 4.42/1.83  ----------------------
% 4.42/1.83  Preprocessing        : 0.32
% 4.42/1.83  Parsing              : 0.17
% 4.42/1.83  CNF conversion       : 0.02
% 4.42/1.83  Main loop            : 0.75
% 4.42/1.83  Inferencing          : 0.24
% 4.42/1.83  Reduction            : 0.31
% 4.42/1.83  Demodulation         : 0.25
% 4.42/1.83  BG Simplification    : 0.03
% 4.42/1.83  Subsumption          : 0.12
% 4.42/1.83  Abstraction          : 0.04
% 4.42/1.83  MUC search           : 0.00
% 4.42/1.83  Cooper               : 0.00
% 4.42/1.83  Total                : 1.10
% 4.42/1.83  Index Insertion      : 0.00
% 4.42/1.83  Index Deletion       : 0.00
% 4.42/1.83  Index Matching       : 0.00
% 4.42/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
