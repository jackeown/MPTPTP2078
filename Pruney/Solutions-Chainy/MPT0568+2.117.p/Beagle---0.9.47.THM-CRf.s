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
% DateTime   : Thu Dec  3 10:01:35 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  81 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_18,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_148,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_1'(A_41,B_42),B_42)
      | r2_hidden('#skF_2'(A_41,B_42),A_41)
      | B_42 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    ! [B_32] : k3_xboole_0(k1_xboole_0,B_32) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_16])).

tff(c_132,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_135,plain,(
    ! [B_32,C_36] :
      ( ~ r1_xboole_0(k1_xboole_0,B_32)
      | ~ r2_hidden(C_36,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_132])).

tff(c_144,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_164,plain,(
    ! [B_42] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_42),B_42)
      | k1_xboole_0 = B_42 ) ),
    inference(resolution,[status(thm)],[c_148,c_144])).

tff(c_51,plain,(
    ! [B_26] : k2_zfmisc_1(k1_xboole_0,B_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_26])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_429,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_4'(A_66,B_67,C_68),k2_relat_1(C_68))
      | ~ r2_hidden(A_66,k10_relat_1(C_68,B_67))
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_432,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_4'(A_66,B_67,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_66,k10_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_429])).

tff(c_434,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_4'(A_66,B_67,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_66,k10_relat_1(k1_xboole_0,B_67)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_432])).

tff(c_436,plain,(
    ! [A_69,B_70] : ~ r2_hidden(A_69,k10_relat_1(k1_xboole_0,B_70)) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_434])).

tff(c_461,plain,(
    ! [B_70] : k10_relat_1(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_164,c_436])).

tff(c_40,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_40])).

tff(c_470,plain,(
    ! [B_71] : ~ r1_xboole_0(k1_xboole_0,B_71) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_475,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.18/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.18/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.18/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.31  
% 2.18/1.32  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.18/1.32  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.18/1.32  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.18/1.32  tff(f_50, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.18/1.32  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.18/1.32  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.18/1.32  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.32  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.18/1.32  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.18/1.32  tff(f_77, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.18/1.32  tff(c_18, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.32  tff(c_148, plain, (![A_41, B_42]: (r2_hidden('#skF_1'(A_41, B_42), B_42) | r2_hidden('#skF_2'(A_41, B_42), A_41) | B_42=A_41)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.32  tff(c_96, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.18/1.32  tff(c_16, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.32  tff(c_106, plain, (![B_32]: (k3_xboole_0(k1_xboole_0, B_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_16])).
% 2.18/1.32  tff(c_132, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.32  tff(c_135, plain, (![B_32, C_36]: (~r1_xboole_0(k1_xboole_0, B_32) | ~r2_hidden(C_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_106, c_132])).
% 2.18/1.32  tff(c_144, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_135])).
% 2.18/1.32  tff(c_164, plain, (![B_42]: (r2_hidden('#skF_1'(k1_xboole_0, B_42), B_42) | k1_xboole_0=B_42)), inference(resolution, [status(thm)], [c_148, c_144])).
% 2.18/1.32  tff(c_51, plain, (![B_26]: (k2_zfmisc_1(k1_xboole_0, B_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.32  tff(c_26, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.18/1.32  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_51, c_26])).
% 2.18/1.32  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.32  tff(c_429, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_4'(A_66, B_67, C_68), k2_relat_1(C_68)) | ~r2_hidden(A_66, k10_relat_1(C_68, B_67)) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.32  tff(c_432, plain, (![A_66, B_67]: (r2_hidden('#skF_4'(A_66, B_67, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_66, k10_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_429])).
% 2.18/1.32  tff(c_434, plain, (![A_66, B_67]: (r2_hidden('#skF_4'(A_66, B_67, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_66, k10_relat_1(k1_xboole_0, B_67)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_432])).
% 2.18/1.32  tff(c_436, plain, (![A_69, B_70]: (~r2_hidden(A_69, k10_relat_1(k1_xboole_0, B_70)))), inference(negUnitSimplification, [status(thm)], [c_144, c_434])).
% 2.18/1.32  tff(c_461, plain, (![B_70]: (k10_relat_1(k1_xboole_0, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_164, c_436])).
% 2.18/1.32  tff(c_40, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.32  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_40])).
% 2.18/1.32  tff(c_470, plain, (![B_71]: (~r1_xboole_0(k1_xboole_0, B_71))), inference(splitRight, [status(thm)], [c_135])).
% 2.18/1.32  tff(c_475, plain, $false, inference(resolution, [status(thm)], [c_18, c_470])).
% 2.18/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  Inference rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Ref     : 0
% 2.18/1.32  #Sup     : 97
% 2.18/1.32  #Fact    : 0
% 2.18/1.32  #Define  : 0
% 2.18/1.32  #Split   : 1
% 2.18/1.32  #Chain   : 0
% 2.18/1.32  #Close   : 0
% 2.18/1.32  
% 2.18/1.32  Ordering : KBO
% 2.18/1.32  
% 2.18/1.32  Simplification rules
% 2.18/1.32  ----------------------
% 2.18/1.32  #Subsume      : 11
% 2.18/1.32  #Demod        : 44
% 2.18/1.32  #Tautology    : 55
% 2.18/1.32  #SimpNegUnit  : 3
% 2.18/1.33  #BackRed      : 2
% 2.18/1.33  
% 2.18/1.33  #Partial instantiations: 0
% 2.18/1.33  #Strategies tried      : 1
% 2.18/1.33  
% 2.18/1.33  Timing (in seconds)
% 2.18/1.33  ----------------------
% 2.18/1.33  Preprocessing        : 0.30
% 2.18/1.33  Parsing              : 0.16
% 2.18/1.33  CNF conversion       : 0.02
% 2.18/1.33  Main loop            : 0.26
% 2.18/1.33  Inferencing          : 0.11
% 2.18/1.33  Reduction            : 0.08
% 2.18/1.33  Demodulation         : 0.06
% 2.18/1.33  BG Simplification    : 0.01
% 2.18/1.33  Subsumption          : 0.04
% 2.18/1.33  Abstraction          : 0.01
% 2.18/1.33  MUC search           : 0.00
% 2.18/1.33  Cooper               : 0.00
% 2.18/1.33  Total                : 0.59
% 2.18/1.33  Index Insertion      : 0.00
% 2.18/1.33  Index Deletion       : 0.00
% 2.18/1.33  Index Matching       : 0.00
% 2.18/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
