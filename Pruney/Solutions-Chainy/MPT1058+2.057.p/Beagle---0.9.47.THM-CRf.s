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
% DateTime   : Thu Dec  3 10:17:29 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   70 (  88 expanded)
%              Number of leaves         :   35 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 127 expanded)
%              Number of equality atoms :   38 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_89,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_4') != k10_relat_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_823,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(A_110,'#skF_1'(A_110,B_111,C_112))
      | k2_xboole_0(A_110,C_112) = B_111
      | ~ r1_tarski(C_112,B_111)
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [B_6,A_5,C_7] :
      ( ~ r1_tarski(B_6,'#skF_1'(A_5,B_6,C_7))
      | k2_xboole_0(A_5,C_7) = B_6
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_827,plain,(
    ! [B_111,C_112] :
      ( k2_xboole_0(B_111,C_112) = B_111
      | ~ r1_tarski(C_112,B_111)
      | ~ r1_tarski(B_111,B_111) ) ),
    inference(resolution,[status(thm)],[c_823,c_10])).

tff(c_838,plain,(
    ! [B_113,C_114] :
      ( k2_xboole_0(B_113,C_114) = B_113
      | ~ r1_tarski(C_114,B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_827])).

tff(c_865,plain,(
    k2_xboole_0('#skF_3',k10_relat_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_838])).

tff(c_36,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_146,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k10_relat_1(B_54,A_55),k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    ! [A_29,A_55] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_29),A_55),A_29)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_146])).

tff(c_168,plain,(
    ! [A_56,A_57] : r1_tarski(k10_relat_1(k6_relat_1(A_56),A_57),A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_160])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_182,plain,(
    ! [A_56,A_57] : k2_xboole_0(k10_relat_1(k6_relat_1(A_56),A_57),A_56) = A_56 ),
    inference(resolution,[status(thm)],[c_168,c_8])).

tff(c_34,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_113,plain,(
    ! [A_50] :
      ( k10_relat_1(A_50,k2_relat_1(A_50)) = k1_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,(
    ! [A_29] :
      ( k10_relat_1(k6_relat_1(A_29),A_29) = k1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_113])).

tff(c_126,plain,(
    ! [A_29] : k10_relat_1(k6_relat_1(A_29),A_29) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_122])).

tff(c_433,plain,(
    ! [C_90,A_91,B_92] :
      ( k2_xboole_0(k10_relat_1(C_90,A_91),k10_relat_1(C_90,B_92)) = k10_relat_1(C_90,k2_xboole_0(A_91,B_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_461,plain,(
    ! [A_29,A_91] :
      ( k2_xboole_0(k10_relat_1(k6_relat_1(A_29),A_91),A_29) = k10_relat_1(k6_relat_1(A_29),k2_xboole_0(A_91,A_29))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_433])).

tff(c_591,plain,(
    ! [A_99,A_100] : k10_relat_1(k6_relat_1(A_99),k2_xboole_0(A_100,A_99)) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_182,c_461])).

tff(c_42,plain,(
    ! [B_35,A_34] : k5_relat_1(k6_relat_1(B_35),k6_relat_1(A_34)) = k6_relat_1(k3_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_268,plain,(
    ! [A_73,B_74] :
      ( k10_relat_1(A_73,k1_relat_1(B_74)) = k1_relat_1(k5_relat_1(A_73,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_303,plain,(
    ! [A_73,A_29] :
      ( k1_relat_1(k5_relat_1(A_73,k6_relat_1(A_29))) = k10_relat_1(A_73,A_29)
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_268])).

tff(c_404,plain,(
    ! [A_88,A_89] :
      ( k1_relat_1(k5_relat_1(A_88,k6_relat_1(A_89))) = k10_relat_1(A_88,A_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_303])).

tff(c_426,plain,(
    ! [A_34,B_35] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_34,B_35))) = k10_relat_1(k6_relat_1(B_35),A_34)
      | ~ v1_relat_1(k6_relat_1(B_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_404])).

tff(c_432,plain,(
    ! [B_35,A_34] : k10_relat_1(k6_relat_1(B_35),A_34) = k3_xboole_0(A_34,B_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_426])).

tff(c_597,plain,(
    ! [A_100,A_99] : k3_xboole_0(k2_xboole_0(A_100,A_99),A_99) = A_99 ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_432])).

tff(c_874,plain,(
    k3_xboole_0('#skF_3',k10_relat_1('#skF_2','#skF_4')) = k10_relat_1('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_597])).

tff(c_40,plain,(
    ! [A_31,C_33,B_32] :
      ( k3_xboole_0(A_31,k10_relat_1(C_33,B_32)) = k10_relat_1(k7_relat_1(C_33,A_31),B_32)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_929,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_4') = k10_relat_1('#skF_2','#skF_4')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_40])).

tff(c_941,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_4') = k10_relat_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_929])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.43  
% 2.65/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.43  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.65/1.43  
% 2.65/1.43  %Foreground sorts:
% 2.65/1.43  
% 2.65/1.43  
% 2.65/1.43  %Background operators:
% 2.65/1.43  
% 2.65/1.43  
% 2.65/1.43  %Foreground operators:
% 2.65/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.65/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.65/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.65/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.65/1.43  
% 2.65/1.45  tff(f_99, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.65/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.45  tff(f_48, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 2.65/1.45  tff(f_83, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.65/1.45  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.65/1.45  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.65/1.45  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.65/1.45  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.65/1.45  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 2.65/1.45  tff(f_89, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.65/1.45  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.65/1.45  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.65/1.45  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_4')!=k10_relat_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.45  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.45  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.65/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.45  tff(c_823, plain, (![A_110, B_111, C_112]: (r1_tarski(A_110, '#skF_1'(A_110, B_111, C_112)) | k2_xboole_0(A_110, C_112)=B_111 | ~r1_tarski(C_112, B_111) | ~r1_tarski(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.65/1.45  tff(c_10, plain, (![B_6, A_5, C_7]: (~r1_tarski(B_6, '#skF_1'(A_5, B_6, C_7)) | k2_xboole_0(A_5, C_7)=B_6 | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.65/1.45  tff(c_827, plain, (![B_111, C_112]: (k2_xboole_0(B_111, C_112)=B_111 | ~r1_tarski(C_112, B_111) | ~r1_tarski(B_111, B_111))), inference(resolution, [status(thm)], [c_823, c_10])).
% 2.65/1.45  tff(c_838, plain, (![B_113, C_114]: (k2_xboole_0(B_113, C_114)=B_113 | ~r1_tarski(C_114, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_827])).
% 2.65/1.45  tff(c_865, plain, (k2_xboole_0('#skF_3', k10_relat_1('#skF_2', '#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_838])).
% 2.65/1.45  tff(c_36, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.65/1.45  tff(c_32, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.45  tff(c_146, plain, (![B_54, A_55]: (r1_tarski(k10_relat_1(B_54, A_55), k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.45  tff(c_160, plain, (![A_29, A_55]: (r1_tarski(k10_relat_1(k6_relat_1(A_29), A_55), A_29) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_146])).
% 2.65/1.45  tff(c_168, plain, (![A_56, A_57]: (r1_tarski(k10_relat_1(k6_relat_1(A_56), A_57), A_56))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_160])).
% 2.65/1.45  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.45  tff(c_182, plain, (![A_56, A_57]: (k2_xboole_0(k10_relat_1(k6_relat_1(A_56), A_57), A_56)=A_56)), inference(resolution, [status(thm)], [c_168, c_8])).
% 2.65/1.45  tff(c_34, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.45  tff(c_113, plain, (![A_50]: (k10_relat_1(A_50, k2_relat_1(A_50))=k1_relat_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.65/1.45  tff(c_122, plain, (![A_29]: (k10_relat_1(k6_relat_1(A_29), A_29)=k1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_113])).
% 2.65/1.45  tff(c_126, plain, (![A_29]: (k10_relat_1(k6_relat_1(A_29), A_29)=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_122])).
% 2.65/1.45  tff(c_433, plain, (![C_90, A_91, B_92]: (k2_xboole_0(k10_relat_1(C_90, A_91), k10_relat_1(C_90, B_92))=k10_relat_1(C_90, k2_xboole_0(A_91, B_92)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.65/1.45  tff(c_461, plain, (![A_29, A_91]: (k2_xboole_0(k10_relat_1(k6_relat_1(A_29), A_91), A_29)=k10_relat_1(k6_relat_1(A_29), k2_xboole_0(A_91, A_29)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_433])).
% 2.65/1.45  tff(c_591, plain, (![A_99, A_100]: (k10_relat_1(k6_relat_1(A_99), k2_xboole_0(A_100, A_99))=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_182, c_461])).
% 2.65/1.45  tff(c_42, plain, (![B_35, A_34]: (k5_relat_1(k6_relat_1(B_35), k6_relat_1(A_34))=k6_relat_1(k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.65/1.45  tff(c_268, plain, (![A_73, B_74]: (k10_relat_1(A_73, k1_relat_1(B_74))=k1_relat_1(k5_relat_1(A_73, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.45  tff(c_303, plain, (![A_73, A_29]: (k1_relat_1(k5_relat_1(A_73, k6_relat_1(A_29)))=k10_relat_1(A_73, A_29) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_32, c_268])).
% 2.65/1.45  tff(c_404, plain, (![A_88, A_89]: (k1_relat_1(k5_relat_1(A_88, k6_relat_1(A_89)))=k10_relat_1(A_88, A_89) | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_303])).
% 2.65/1.45  tff(c_426, plain, (![A_34, B_35]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_34, B_35)))=k10_relat_1(k6_relat_1(B_35), A_34) | ~v1_relat_1(k6_relat_1(B_35)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_404])).
% 2.65/1.45  tff(c_432, plain, (![B_35, A_34]: (k10_relat_1(k6_relat_1(B_35), A_34)=k3_xboole_0(A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_426])).
% 2.65/1.45  tff(c_597, plain, (![A_100, A_99]: (k3_xboole_0(k2_xboole_0(A_100, A_99), A_99)=A_99)), inference(superposition, [status(thm), theory('equality')], [c_591, c_432])).
% 2.65/1.45  tff(c_874, plain, (k3_xboole_0('#skF_3', k10_relat_1('#skF_2', '#skF_4'))=k10_relat_1('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_865, c_597])).
% 2.65/1.45  tff(c_40, plain, (![A_31, C_33, B_32]: (k3_xboole_0(A_31, k10_relat_1(C_33, B_32))=k10_relat_1(k7_relat_1(C_33, A_31), B_32) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.45  tff(c_929, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_4')=k10_relat_1('#skF_2', '#skF_4') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_874, c_40])).
% 2.65/1.45  tff(c_941, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_4')=k10_relat_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_929])).
% 2.65/1.45  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_941])).
% 2.65/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.45  
% 2.65/1.45  Inference rules
% 2.65/1.45  ----------------------
% 2.65/1.45  #Ref     : 0
% 2.65/1.45  #Sup     : 206
% 2.65/1.45  #Fact    : 0
% 2.65/1.45  #Define  : 0
% 2.65/1.45  #Split   : 1
% 2.65/1.45  #Chain   : 0
% 2.65/1.45  #Close   : 0
% 2.65/1.45  
% 2.65/1.45  Ordering : KBO
% 2.65/1.45  
% 2.65/1.45  Simplification rules
% 2.65/1.45  ----------------------
% 2.65/1.45  #Subsume      : 3
% 2.65/1.45  #Demod        : 158
% 2.65/1.45  #Tautology    : 117
% 2.65/1.45  #SimpNegUnit  : 1
% 2.65/1.45  #BackRed      : 3
% 2.65/1.45  
% 2.65/1.45  #Partial instantiations: 0
% 2.65/1.45  #Strategies tried      : 1
% 2.65/1.45  
% 2.65/1.45  Timing (in seconds)
% 2.65/1.45  ----------------------
% 2.65/1.45  Preprocessing        : 0.31
% 2.65/1.45  Parsing              : 0.16
% 2.65/1.45  CNF conversion       : 0.02
% 2.65/1.45  Main loop            : 0.34
% 2.65/1.45  Inferencing          : 0.13
% 2.65/1.45  Reduction            : 0.11
% 2.65/1.45  Demodulation         : 0.08
% 2.65/1.45  BG Simplification    : 0.02
% 2.65/1.45  Subsumption          : 0.05
% 2.65/1.45  Abstraction          : 0.02
% 2.65/1.45  MUC search           : 0.00
% 2.65/1.45  Cooper               : 0.00
% 2.65/1.45  Total                : 0.68
% 2.65/1.45  Index Insertion      : 0.00
% 2.65/1.45  Index Deletion       : 0.00
% 2.65/1.45  Index Matching       : 0.00
% 2.65/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
