%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:22 EST 2020

% Result     : Theorem 10.05s
% Output     : CNFRefutation 10.05s
% Verified   : 
% Statistics : Number of formulae       :   65 (  92 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 137 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_270,plain,(
    ! [A_96,B_97,C_98,D_99] : k3_enumset1(A_96,A_96,B_97,C_98,D_99) = k2_enumset1(A_96,B_97,C_98,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [D_21,G_26,A_18,C_20,B_19] : r2_hidden(G_26,k3_enumset1(A_18,B_19,C_20,D_21,G_26)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_371,plain,(
    ! [D_117,A_118,B_119,C_120] : r2_hidden(D_117,k2_enumset1(A_118,B_119,C_120,D_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_18])).

tff(c_378,plain,(
    ! [C_121,A_122,B_123] : r2_hidden(C_121,k1_enumset1(A_122,B_123,C_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_371])).

tff(c_402,plain,(
    ! [B_125,A_126] : r2_hidden(B_125,k2_tarski(A_126,B_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_378])).

tff(c_52,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k1_setfam_1(B_45),A_46)
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_107,plain,(
    ! [A_27,B_28,A_46] :
      ( r1_tarski(k3_xboole_0(A_27,B_28),A_46)
      | ~ r2_hidden(A_46,k2_tarski(A_27,B_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_104])).

tff(c_410,plain,(
    ! [A_127,B_128] : r1_tarski(k3_xboole_0(A_127,B_128),B_128) ),
    inference(resolution,[status(thm)],[c_402,c_107])).

tff(c_70,plain,(
    r2_hidden('#skF_4',k3_xboole_0(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_235,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_4',B_90)
      | ~ r1_tarski(k3_xboole_0(k1_relat_1('#skF_6'),'#skF_5'),B_90) ) ),
    inference(resolution,[status(thm)],[c_70,c_235])).

tff(c_415,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_410,c_256])).

tff(c_66,plain,(
    ! [B_38,A_37] :
      ( k1_funct_1(k6_relat_1(B_38),A_37) = A_37
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_74,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,(
    ! [A_32] : v1_funct_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56,plain,(
    ! [A_31] : k1_relat_1(k6_relat_1(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_440,plain,(
    ! [B_132,C_133,A_134] :
      ( k1_funct_1(k5_relat_1(B_132,C_133),A_134) = k1_funct_1(C_133,k1_funct_1(B_132,A_134))
      | ~ r2_hidden(A_134,k1_relat_1(B_132))
      | ~ v1_funct_1(C_133)
      | ~ v1_relat_1(C_133)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_447,plain,(
    ! [A_31,C_133,A_134] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_31),C_133),A_134) = k1_funct_1(C_133,k1_funct_1(k6_relat_1(A_31),A_134))
      | ~ r2_hidden(A_134,A_31)
      | ~ v1_funct_1(C_133)
      | ~ v1_relat_1(C_133)
      | ~ v1_funct_1(k6_relat_1(A_31))
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_440])).

tff(c_11090,plain,(
    ! [A_29850,C_29851,A_29852] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_29850),C_29851),A_29852) = k1_funct_1(C_29851,k1_funct_1(k6_relat_1(A_29850),A_29852))
      | ~ r2_hidden(A_29852,A_29850)
      | ~ v1_funct_1(C_29851)
      | ~ v1_relat_1(C_29851) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_447])).

tff(c_68,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_11096,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11090,c_68])).

tff(c_11117,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_415,c_11096])).

tff(c_11131,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_11117])).

tff(c_11135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_11131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:07:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.05/3.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.05/3.57  
% 10.05/3.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.05/3.58  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 10.05/3.58  
% 10.05/3.58  %Foreground sorts:
% 10.05/3.58  
% 10.05/3.58  
% 10.05/3.58  %Background operators:
% 10.05/3.58  
% 10.05/3.58  
% 10.05/3.58  %Foreground operators:
% 10.05/3.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.05/3.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.05/3.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 10.05/3.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.05/3.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.05/3.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.05/3.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.05/3.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.05/3.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.05/3.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.05/3.58  tff('#skF_5', type, '#skF_5': $i).
% 10.05/3.58  tff('#skF_6', type, '#skF_6': $i).
% 10.05/3.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.05/3.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.05/3.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 10.05/3.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.05/3.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.05/3.58  tff('#skF_4', type, '#skF_4': $i).
% 10.05/3.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.05/3.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.05/3.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.05/3.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.05/3.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.05/3.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.05/3.58  
% 10.05/3.59  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.05/3.59  tff(f_38, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 10.05/3.59  tff(f_40, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 10.05/3.59  tff(f_61, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 10.05/3.59  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.05/3.59  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 10.05/3.59  tff(f_101, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 10.05/3.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.05/3.59  tff(f_92, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 10.05/3.59  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.05/3.59  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.05/3.59  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 10.05/3.59  tff(c_10, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.05/3.59  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.05/3.59  tff(c_270, plain, (![A_96, B_97, C_98, D_99]: (k3_enumset1(A_96, A_96, B_97, C_98, D_99)=k2_enumset1(A_96, B_97, C_98, D_99))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.05/3.59  tff(c_18, plain, (![D_21, G_26, A_18, C_20, B_19]: (r2_hidden(G_26, k3_enumset1(A_18, B_19, C_20, D_21, G_26)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.05/3.59  tff(c_371, plain, (![D_117, A_118, B_119, C_120]: (r2_hidden(D_117, k2_enumset1(A_118, B_119, C_120, D_117)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_18])).
% 10.05/3.59  tff(c_378, plain, (![C_121, A_122, B_123]: (r2_hidden(C_121, k1_enumset1(A_122, B_123, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_371])).
% 10.05/3.59  tff(c_402, plain, (![B_125, A_126]: (r2_hidden(B_125, k2_tarski(A_126, B_125)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_378])).
% 10.05/3.59  tff(c_52, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.05/3.59  tff(c_104, plain, (![B_45, A_46]: (r1_tarski(k1_setfam_1(B_45), A_46) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.05/3.59  tff(c_107, plain, (![A_27, B_28, A_46]: (r1_tarski(k3_xboole_0(A_27, B_28), A_46) | ~r2_hidden(A_46, k2_tarski(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_104])).
% 10.05/3.59  tff(c_410, plain, (![A_127, B_128]: (r1_tarski(k3_xboole_0(A_127, B_128), B_128))), inference(resolution, [status(thm)], [c_402, c_107])).
% 10.05/3.59  tff(c_70, plain, (r2_hidden('#skF_4', k3_xboole_0(k1_relat_1('#skF_6'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.05/3.59  tff(c_235, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.05/3.59  tff(c_256, plain, (![B_90]: (r2_hidden('#skF_4', B_90) | ~r1_tarski(k3_xboole_0(k1_relat_1('#skF_6'), '#skF_5'), B_90))), inference(resolution, [status(thm)], [c_70, c_235])).
% 10.05/3.59  tff(c_415, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_410, c_256])).
% 10.05/3.59  tff(c_66, plain, (![B_38, A_37]: (k1_funct_1(k6_relat_1(B_38), A_37)=A_37 | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.05/3.59  tff(c_74, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.05/3.59  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.05/3.59  tff(c_60, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.05/3.59  tff(c_62, plain, (![A_32]: (v1_funct_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.05/3.59  tff(c_56, plain, (![A_31]: (k1_relat_1(k6_relat_1(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.05/3.59  tff(c_440, plain, (![B_132, C_133, A_134]: (k1_funct_1(k5_relat_1(B_132, C_133), A_134)=k1_funct_1(C_133, k1_funct_1(B_132, A_134)) | ~r2_hidden(A_134, k1_relat_1(B_132)) | ~v1_funct_1(C_133) | ~v1_relat_1(C_133) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.05/3.59  tff(c_447, plain, (![A_31, C_133, A_134]: (k1_funct_1(k5_relat_1(k6_relat_1(A_31), C_133), A_134)=k1_funct_1(C_133, k1_funct_1(k6_relat_1(A_31), A_134)) | ~r2_hidden(A_134, A_31) | ~v1_funct_1(C_133) | ~v1_relat_1(C_133) | ~v1_funct_1(k6_relat_1(A_31)) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_440])).
% 10.05/3.59  tff(c_11090, plain, (![A_29850, C_29851, A_29852]: (k1_funct_1(k5_relat_1(k6_relat_1(A_29850), C_29851), A_29852)=k1_funct_1(C_29851, k1_funct_1(k6_relat_1(A_29850), A_29852)) | ~r2_hidden(A_29852, A_29850) | ~v1_funct_1(C_29851) | ~v1_relat_1(C_29851))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_447])).
% 10.05/3.59  tff(c_68, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_5'), '#skF_6'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.05/3.59  tff(c_11096, plain, (k1_funct_1('#skF_6', k1_funct_1(k6_relat_1('#skF_5'), '#skF_4'))!=k1_funct_1('#skF_6', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11090, c_68])).
% 10.05/3.59  tff(c_11117, plain, (k1_funct_1('#skF_6', k1_funct_1(k6_relat_1('#skF_5'), '#skF_4'))!=k1_funct_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_415, c_11096])).
% 10.05/3.59  tff(c_11131, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_66, c_11117])).
% 10.05/3.59  tff(c_11135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_415, c_11131])).
% 10.05/3.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.05/3.59  
% 10.05/3.59  Inference rules
% 10.05/3.59  ----------------------
% 10.05/3.59  #Ref     : 0
% 10.05/3.59  #Sup     : 1819
% 10.05/3.59  #Fact    : 104
% 10.05/3.59  #Define  : 0
% 10.05/3.59  #Split   : 2
% 10.05/3.59  #Chain   : 0
% 10.05/3.59  #Close   : 0
% 10.05/3.59  
% 10.05/3.59  Ordering : KBO
% 10.05/3.59  
% 10.05/3.59  Simplification rules
% 10.05/3.59  ----------------------
% 10.05/3.59  #Subsume      : 687
% 10.05/3.59  #Demod        : 109
% 10.05/3.59  #Tautology    : 280
% 10.05/3.59  #SimpNegUnit  : 0
% 10.05/3.59  #BackRed      : 0
% 10.05/3.59  
% 10.05/3.59  #Partial instantiations: 13260
% 10.05/3.59  #Strategies tried      : 1
% 10.05/3.59  
% 10.05/3.59  Timing (in seconds)
% 10.05/3.59  ----------------------
% 10.05/3.59  Preprocessing        : 0.35
% 10.05/3.59  Parsing              : 0.18
% 10.05/3.59  CNF conversion       : 0.03
% 10.05/3.59  Main loop            : 2.52
% 10.05/3.59  Inferencing          : 1.31
% 10.05/3.59  Reduction            : 0.48
% 10.05/3.59  Demodulation         : 0.37
% 10.05/3.59  BG Simplification    : 0.12
% 10.05/3.59  Subsumption          : 0.50
% 10.05/3.59  Abstraction          : 0.21
% 10.05/3.59  MUC search           : 0.00
% 10.05/3.59  Cooper               : 0.00
% 10.05/3.59  Total                : 2.89
% 10.05/3.59  Index Insertion      : 0.00
% 10.05/3.59  Index Deletion       : 0.00
% 10.05/3.59  Index Matching       : 0.00
% 10.05/3.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
