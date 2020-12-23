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
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 157 expanded)
%              Number of equality atoms :   29 (  69 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_94,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_44,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_88,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_2'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_168,plain,(
    ! [C_66,A_67] :
      ( r2_hidden(k4_tarski(C_66,'#skF_6'(A_67,k1_relat_1(A_67),C_66)),A_67)
      | ~ r2_hidden(C_66,k1_relat_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_112,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,k3_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_119,plain,(
    ! [A_9,C_51] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_51,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_112])).

tff(c_122,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_187,plain,(
    ! [C_71] : ~ r2_hidden(C_71,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_168,c_122])).

tff(c_195,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_187])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_195])).

tff(c_201,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_60,plain,(
    ! [B_42] : k2_zfmisc_1(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_202,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_34,plain,(
    ! [A_32] :
      ( v1_relat_1(k4_relat_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    ! [A_36] :
      ( k2_relat_1(k4_relat_1(A_36)) = k1_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_226,plain,(
    ! [A_75] :
      ( ~ v1_xboole_0(k2_relat_1(A_75))
      | ~ v1_relat_1(A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_380,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(k1_relat_1(A_101))
      | ~ v1_relat_1(k4_relat_1(A_101))
      | v1_xboole_0(k4_relat_1(A_101))
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_226])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_386,plain,(
    ! [A_104] :
      ( k4_relat_1(A_104) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_104))
      | ~ v1_relat_1(k4_relat_1(A_104))
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_380,c_4])).

tff(c_398,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_386])).

tff(c_404,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2,c_398])).

tff(c_405,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_408,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_405])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_408])).

tff(c_413,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_42,plain,(
    ! [A_36] :
      ( k1_relat_1(k4_relat_1(A_36)) = k2_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_421,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_42])).

tff(c_433,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_202,c_421])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.12/1.31  
% 2.12/1.31  %Foreground sorts:
% 2.12/1.31  
% 2.12/1.31  
% 2.12/1.31  %Background operators:
% 2.12/1.31  
% 2.12/1.31  
% 2.12/1.31  %Foreground operators:
% 2.12/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.12/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.12/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.12/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.12/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.31  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.12/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.12/1.31  
% 2.12/1.32  tff(f_94, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.32  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.12/1.32  tff(f_70, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.12/1.32  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.32  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.32  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.32  tff(f_62, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.12/1.32  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.12/1.32  tff(f_74, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.12/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.32  tff(f_90, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.12/1.32  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.12/1.32  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.12/1.32  tff(c_44, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.12/1.32  tff(c_88, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 2.12/1.32  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_2'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.32  tff(c_168, plain, (![C_66, A_67]: (r2_hidden(k4_tarski(C_66, '#skF_6'(A_67, k1_relat_1(A_67), C_66)), A_67) | ~r2_hidden(C_66, k1_relat_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.32  tff(c_14, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.32  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.32  tff(c_112, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.32  tff(c_119, plain, (![A_9, C_51]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_112])).
% 2.12/1.32  tff(c_122, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_119])).
% 2.12/1.32  tff(c_187, plain, (![C_71]: (~r2_hidden(C_71, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_168, c_122])).
% 2.12/1.32  tff(c_195, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_187])).
% 2.12/1.32  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_195])).
% 2.12/1.32  tff(c_201, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.12/1.32  tff(c_60, plain, (![B_42]: (k2_zfmisc_1(k1_xboole_0, B_42)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.12/1.32  tff(c_36, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.12/1.32  tff(c_64, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_36])).
% 2.12/1.32  tff(c_202, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.12/1.32  tff(c_34, plain, (![A_32]: (v1_relat_1(k4_relat_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.12/1.32  tff(c_40, plain, (![A_36]: (k2_relat_1(k4_relat_1(A_36))=k1_relat_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.12/1.32  tff(c_226, plain, (![A_75]: (~v1_xboole_0(k2_relat_1(A_75)) | ~v1_relat_1(A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.32  tff(c_380, plain, (![A_101]: (~v1_xboole_0(k1_relat_1(A_101)) | ~v1_relat_1(k4_relat_1(A_101)) | v1_xboole_0(k4_relat_1(A_101)) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_40, c_226])).
% 2.12/1.32  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.12/1.32  tff(c_386, plain, (![A_104]: (k4_relat_1(A_104)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_104)) | ~v1_relat_1(k4_relat_1(A_104)) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_380, c_4])).
% 2.12/1.32  tff(c_398, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_202, c_386])).
% 2.12/1.32  tff(c_404, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2, c_398])).
% 2.12/1.32  tff(c_405, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_404])).
% 2.12/1.32  tff(c_408, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_405])).
% 2.12/1.32  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_408])).
% 2.12/1.32  tff(c_413, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_404])).
% 2.12/1.32  tff(c_42, plain, (![A_36]: (k1_relat_1(k4_relat_1(A_36))=k2_relat_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.12/1.32  tff(c_421, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_413, c_42])).
% 2.12/1.32  tff(c_433, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_202, c_421])).
% 2.12/1.32  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_433])).
% 2.12/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.32  
% 2.12/1.32  Inference rules
% 2.12/1.32  ----------------------
% 2.12/1.32  #Ref     : 0
% 2.12/1.32  #Sup     : 82
% 2.12/1.32  #Fact    : 0
% 2.12/1.32  #Define  : 0
% 2.12/1.32  #Split   : 2
% 2.12/1.32  #Chain   : 0
% 2.12/1.32  #Close   : 0
% 2.12/1.32  
% 2.12/1.32  Ordering : KBO
% 2.12/1.32  
% 2.12/1.32  Simplification rules
% 2.12/1.32  ----------------------
% 2.12/1.32  #Subsume      : 9
% 2.12/1.32  #Demod        : 34
% 2.12/1.32  #Tautology    : 43
% 2.12/1.32  #SimpNegUnit  : 5
% 2.12/1.32  #BackRed      : 0
% 2.12/1.32  
% 2.12/1.32  #Partial instantiations: 0
% 2.12/1.32  #Strategies tried      : 1
% 2.12/1.32  
% 2.12/1.32  Timing (in seconds)
% 2.12/1.32  ----------------------
% 2.34/1.33  Preprocessing        : 0.28
% 2.34/1.33  Parsing              : 0.15
% 2.34/1.33  CNF conversion       : 0.02
% 2.34/1.33  Main loop            : 0.23
% 2.34/1.33  Inferencing          : 0.09
% 2.34/1.33  Reduction            : 0.06
% 2.34/1.33  Demodulation         : 0.04
% 2.34/1.33  BG Simplification    : 0.01
% 2.34/1.33  Subsumption          : 0.04
% 2.34/1.33  Abstraction          : 0.01
% 2.34/1.33  MUC search           : 0.00
% 2.34/1.33  Cooper               : 0.00
% 2.34/1.33  Total                : 0.54
% 2.34/1.33  Index Insertion      : 0.00
% 2.34/1.33  Index Deletion       : 0.00
% 2.34/1.33  Index Matching       : 0.00
% 2.34/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
