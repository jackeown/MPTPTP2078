%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:33 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   58 (  74 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 114 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_146,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_149,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    ! [B_33,A_32] :
      ( r1_xboole_0(B_33,k1_tarski(A_32))
      | r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_149,c_4])).

tff(c_214,plain,(
    ! [B_50,A_51] :
      ( k10_relat_1(B_50,A_51) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_324,plain,(
    ! [B_67,A_68] :
      ( k10_relat_1(B_67,k1_tarski(A_68)) = k1_xboole_0
      | ~ v1_relat_1(B_67)
      | r2_hidden(A_68,k2_relat_1(B_67)) ) ),
    inference(resolution,[status(thm)],[c_152,c_214])).

tff(c_32,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_181,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_32])).

tff(c_330,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_324,c_181])).

tff(c_334,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_330])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_334])).

tff(c_337,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_340,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_32])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_362,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,k3_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_374,plain,(
    ! [A_10,C_79] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_79,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_362])).

tff(c_378,plain,(
    ! [C_79] : ~ r2_hidden(C_79,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_374])).

tff(c_60,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [A_10] : k3_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_60])).

tff(c_380,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(B_81,A_82)
      | k3_xboole_0(A_82,k1_tarski(B_81)) != k1_tarski(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_384,plain,(
    ! [B_81] :
      ( r2_hidden(B_81,k1_xboole_0)
      | k1_tarski(B_81) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_380])).

tff(c_393,plain,(
    ! [B_81] : k1_tarski(B_81) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_384])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_tarski(A_13),B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_514,plain,(
    ! [B_102,A_103] :
      ( k10_relat_1(B_102,A_103) != k1_xboole_0
      | ~ r1_tarski(A_103,k2_relat_1(B_102))
      | k1_xboole_0 = A_103
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_518,plain,(
    ! [B_102,A_13] :
      ( k10_relat_1(B_102,k1_tarski(A_13)) != k1_xboole_0
      | k1_tarski(A_13) = k1_xboole_0
      | ~ v1_relat_1(B_102)
      | ~ r2_hidden(A_13,k2_relat_1(B_102)) ) ),
    inference(resolution,[status(thm)],[c_18,c_514])).

tff(c_522,plain,(
    ! [B_104,A_105] :
      ( k10_relat_1(B_104,k1_tarski(A_105)) != k1_xboole_0
      | ~ v1_relat_1(B_104)
      | ~ r2_hidden(A_105,k2_relat_1(B_104)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_518])).

tff(c_528,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_337,c_522])).

tff(c_533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_340,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.35  
% 2.57/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.36  
% 2.57/1.36  %Foreground sorts:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Background operators:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Foreground operators:
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.57/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.36  
% 2.73/1.37  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.73/1.37  tff(f_60, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.73/1.37  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.73/1.37  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.73/1.37  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.73/1.37  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.73/1.37  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.73/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.73/1.37  tff(f_64, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.73/1.37  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.73/1.37  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.73/1.37  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.37  tff(c_38, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.37  tff(c_146, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.73/1.37  tff(c_149, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.37  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.37  tff(c_152, plain, (![B_33, A_32]: (r1_xboole_0(B_33, k1_tarski(A_32)) | r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_149, c_4])).
% 2.73/1.37  tff(c_214, plain, (![B_50, A_51]: (k10_relat_1(B_50, A_51)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.73/1.37  tff(c_324, plain, (![B_67, A_68]: (k10_relat_1(B_67, k1_tarski(A_68))=k1_xboole_0 | ~v1_relat_1(B_67) | r2_hidden(A_68, k2_relat_1(B_67)))), inference(resolution, [status(thm)], [c_152, c_214])).
% 2.73/1.37  tff(c_32, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.73/1.37  tff(c_181, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_146, c_32])).
% 2.73/1.37  tff(c_330, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_324, c_181])).
% 2.73/1.37  tff(c_334, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_330])).
% 2.73/1.37  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_334])).
% 2.73/1.37  tff(c_337, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_38])).
% 2.73/1.37  tff(c_340, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_337, c_32])).
% 2.73/1.37  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.37  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.37  tff(c_362, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, k3_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.73/1.37  tff(c_374, plain, (![A_10, C_79]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_362])).
% 2.73/1.37  tff(c_378, plain, (![C_79]: (~r2_hidden(C_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_374])).
% 2.73/1.37  tff(c_60, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.37  tff(c_98, plain, (![A_10]: (k3_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_60])).
% 2.73/1.37  tff(c_380, plain, (![B_81, A_82]: (r2_hidden(B_81, A_82) | k3_xboole_0(A_82, k1_tarski(B_81))!=k1_tarski(B_81))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.37  tff(c_384, plain, (![B_81]: (r2_hidden(B_81, k1_xboole_0) | k1_tarski(B_81)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_380])).
% 2.73/1.37  tff(c_393, plain, (![B_81]: (k1_tarski(B_81)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_378, c_384])).
% 2.73/1.37  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k1_tarski(A_13), B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.73/1.37  tff(c_514, plain, (![B_102, A_103]: (k10_relat_1(B_102, A_103)!=k1_xboole_0 | ~r1_tarski(A_103, k2_relat_1(B_102)) | k1_xboole_0=A_103 | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.73/1.37  tff(c_518, plain, (![B_102, A_13]: (k10_relat_1(B_102, k1_tarski(A_13))!=k1_xboole_0 | k1_tarski(A_13)=k1_xboole_0 | ~v1_relat_1(B_102) | ~r2_hidden(A_13, k2_relat_1(B_102)))), inference(resolution, [status(thm)], [c_18, c_514])).
% 2.73/1.37  tff(c_522, plain, (![B_104, A_105]: (k10_relat_1(B_104, k1_tarski(A_105))!=k1_xboole_0 | ~v1_relat_1(B_104) | ~r2_hidden(A_105, k2_relat_1(B_104)))), inference(negUnitSimplification, [status(thm)], [c_393, c_518])).
% 2.73/1.37  tff(c_528, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_337, c_522])).
% 2.73/1.37  tff(c_533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_340, c_528])).
% 2.73/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  Inference rules
% 2.73/1.37  ----------------------
% 2.73/1.37  #Ref     : 0
% 2.73/1.37  #Sup     : 110
% 2.73/1.37  #Fact    : 0
% 2.73/1.37  #Define  : 0
% 2.73/1.37  #Split   : 1
% 2.73/1.37  #Chain   : 0
% 2.73/1.37  #Close   : 0
% 2.73/1.37  
% 2.73/1.37  Ordering : KBO
% 2.73/1.37  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 34
% 2.73/1.38  #Demod        : 31
% 2.73/1.38  #Tautology    : 53
% 2.73/1.38  #SimpNegUnit  : 16
% 2.73/1.38  #BackRed      : 0
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.38  Preprocessing        : 0.32
% 2.73/1.38  Parsing              : 0.16
% 2.73/1.38  CNF conversion       : 0.02
% 2.73/1.38  Main loop            : 0.29
% 2.73/1.38  Inferencing          : 0.11
% 2.73/1.38  Reduction            : 0.09
% 2.73/1.38  Demodulation         : 0.06
% 2.73/1.38  BG Simplification    : 0.01
% 2.73/1.38  Subsumption          : 0.05
% 2.73/1.38  Abstraction          : 0.02
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.64
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
