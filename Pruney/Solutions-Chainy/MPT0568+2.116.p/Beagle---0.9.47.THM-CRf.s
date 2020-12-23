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
% DateTime   : Thu Dec  3 10:01:35 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   50 (  66 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  74 expanded)
%              Number of equality atoms :   19 (  29 expanded)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_252,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r2_hidden('#skF_2'(A_48,B_49),A_48)
      | B_49 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_105,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k3_xboole_0(A_31,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_115,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_141,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_144,plain,(
    ! [C_36] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_36,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_141])).

tff(c_146,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_144])).

tff(c_274,plain,(
    ! [B_49] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_49),B_49)
      | k1_xboole_0 = B_49 ) ),
    inference(resolution,[status(thm)],[c_252,c_146])).

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

tff(c_418,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_4'(A_65,B_66,C_67),k2_relat_1(C_67))
      | ~ r2_hidden(A_65,k10_relat_1(C_67,B_66))
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_421,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_4'(A_65,B_66,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_65,k10_relat_1(k1_xboole_0,B_66))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_418])).

tff(c_423,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_4'(A_65,B_66,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_65,k10_relat_1(k1_xboole_0,B_66)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_421])).

tff(c_425,plain,(
    ! [A_68,B_69] : ~ r2_hidden(A_68,k10_relat_1(k1_xboole_0,B_69)) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_423])).

tff(c_447,plain,(
    ! [B_69] : k10_relat_1(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_274,c_425])).

tff(c_40,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:18:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.30  
% 1.97/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 1.97/1.30  
% 1.97/1.30  %Foreground sorts:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Background operators:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Foreground operators:
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.97/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.97/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.97/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.30  
% 1.97/1.32  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.97/1.32  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.32  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.97/1.32  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.97/1.32  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.97/1.32  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.97/1.32  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.97/1.32  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.97/1.32  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.97/1.32  tff(f_77, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.97/1.32  tff(c_252, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), B_49) | r2_hidden('#skF_2'(A_48, B_49), A_48) | B_49=A_48)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.32  tff(c_18, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.32  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.32  tff(c_87, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.32  tff(c_105, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k3_xboole_0(A_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_87])).
% 1.97/1.32  tff(c_115, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 1.97/1.32  tff(c_141, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.97/1.32  tff(c_144, plain, (![C_36]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_141])).
% 1.97/1.32  tff(c_146, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_144])).
% 1.97/1.32  tff(c_274, plain, (![B_49]: (r2_hidden('#skF_1'(k1_xboole_0, B_49), B_49) | k1_xboole_0=B_49)), inference(resolution, [status(thm)], [c_252, c_146])).
% 1.97/1.32  tff(c_51, plain, (![B_26]: (k2_zfmisc_1(k1_xboole_0, B_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.32  tff(c_26, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.32  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_51, c_26])).
% 1.97/1.32  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.97/1.32  tff(c_418, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_4'(A_65, B_66, C_67), k2_relat_1(C_67)) | ~r2_hidden(A_65, k10_relat_1(C_67, B_66)) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.97/1.32  tff(c_421, plain, (![A_65, B_66]: (r2_hidden('#skF_4'(A_65, B_66, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_65, k10_relat_1(k1_xboole_0, B_66)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_418])).
% 1.97/1.32  tff(c_423, plain, (![A_65, B_66]: (r2_hidden('#skF_4'(A_65, B_66, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_65, k10_relat_1(k1_xboole_0, B_66)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_421])).
% 1.97/1.32  tff(c_425, plain, (![A_68, B_69]: (~r2_hidden(A_68, k10_relat_1(k1_xboole_0, B_69)))), inference(negUnitSimplification, [status(thm)], [c_146, c_423])).
% 1.97/1.32  tff(c_447, plain, (![B_69]: (k10_relat_1(k1_xboole_0, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_274, c_425])).
% 1.97/1.32  tff(c_40, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.97/1.32  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_40])).
% 1.97/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.32  
% 1.97/1.32  Inference rules
% 1.97/1.32  ----------------------
% 1.97/1.32  #Ref     : 0
% 1.97/1.32  #Sup     : 91
% 1.97/1.32  #Fact    : 0
% 1.97/1.32  #Define  : 0
% 1.97/1.32  #Split   : 0
% 1.97/1.32  #Chain   : 0
% 1.97/1.32  #Close   : 0
% 1.97/1.32  
% 1.97/1.32  Ordering : KBO
% 1.97/1.32  
% 1.97/1.32  Simplification rules
% 1.97/1.32  ----------------------
% 1.97/1.32  #Subsume      : 8
% 1.97/1.32  #Demod        : 37
% 1.97/1.32  #Tautology    : 58
% 1.97/1.32  #SimpNegUnit  : 2
% 1.97/1.32  #BackRed      : 5
% 1.97/1.32  
% 1.97/1.32  #Partial instantiations: 0
% 1.97/1.32  #Strategies tried      : 1
% 1.97/1.32  
% 1.97/1.32  Timing (in seconds)
% 1.97/1.32  ----------------------
% 2.27/1.32  Preprocessing        : 0.28
% 2.27/1.32  Parsing              : 0.15
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.27
% 2.27/1.32  Inferencing          : 0.13
% 2.27/1.32  Reduction            : 0.08
% 2.27/1.32  Demodulation         : 0.06
% 2.27/1.32  BG Simplification    : 0.01
% 2.27/1.32  Subsumption          : 0.04
% 2.27/1.32  Abstraction          : 0.01
% 2.27/1.32  MUC search           : 0.00
% 2.27/1.32  Cooper               : 0.00
% 2.27/1.32  Total                : 0.58
% 2.27/1.32  Index Insertion      : 0.00
% 2.27/1.32  Index Deletion       : 0.00
% 2.27/1.32  Index Matching       : 0.00
% 2.27/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
