%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:54 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 103 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 141 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_88,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
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

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_42,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_80,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_172,plain,(
    ! [C_62,A_63] :
      ( r2_hidden(k4_tarski(C_62,'#skF_6'(A_63,k1_relat_1(A_63),C_62)),A_63)
      | ~ r2_hidden(C_62,k1_relat_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [A_8,C_46] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_46,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_99])).

tff(c_109,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_106])).

tff(c_190,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_172,c_109])).

tff(c_198,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_190])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_198])).

tff(c_204,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_51,plain,(
    ! [A_37] :
      ( v1_relat_1(A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_205,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_34,plain,(
    ! [A_32] :
      ( v1_relat_1(k4_relat_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_34] :
      ( k2_relat_1(k4_relat_1(A_34)) = k1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_274,plain,(
    ! [A_80] :
      ( k3_xboole_0(A_80,k2_zfmisc_1(k1_relat_1(A_80),k2_relat_1(A_80))) = A_80
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1904,plain,(
    ! [A_159] :
      ( k3_xboole_0(k4_relat_1(A_159),k2_zfmisc_1(k1_relat_1(k4_relat_1(A_159)),k1_relat_1(A_159))) = k4_relat_1(A_159)
      | ~ v1_relat_1(k4_relat_1(A_159))
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_274])).

tff(c_2015,plain,
    ( k3_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)) = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_1904])).

tff(c_2026,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_10,c_16,c_2015])).

tff(c_2078,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2026])).

tff(c_2081,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_2078])).

tff(c_2085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2081])).

tff(c_2086,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2026])).

tff(c_40,plain,(
    ! [A_34] :
      ( k1_relat_1(k4_relat_1(A_34)) = k2_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2103,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2086,c_40])).

tff(c_2121,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_205,c_2103])).

tff(c_2123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_2121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:51:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.61  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.43/1.61  
% 3.43/1.61  %Foreground sorts:
% 3.43/1.61  
% 3.43/1.61  
% 3.43/1.61  %Background operators:
% 3.43/1.61  
% 3.43/1.61  
% 3.43/1.61  %Foreground operators:
% 3.43/1.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.43/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.43/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.43/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.43/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.43/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.43/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.43/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.61  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.43/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.43/1.61  
% 3.43/1.62  tff(f_88, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.43/1.62  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.43/1.62  tff(f_70, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.43/1.62  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.43/1.62  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.43/1.62  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.43/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.43/1.62  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.43/1.62  tff(f_74, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.43/1.62  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.43/1.62  tff(f_84, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.43/1.62  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.43/1.62  tff(c_42, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.43/1.62  tff(c_80, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.43/1.62  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.43/1.62  tff(c_172, plain, (![C_62, A_63]: (r2_hidden(k4_tarski(C_62, '#skF_6'(A_63, k1_relat_1(A_63), C_62)), A_63) | ~r2_hidden(C_62, k1_relat_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.43/1.62  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.62  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.62  tff(c_99, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.43/1.62  tff(c_106, plain, (![A_8, C_46]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_99])).
% 3.43/1.62  tff(c_109, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_106])).
% 3.43/1.62  tff(c_190, plain, (![C_64]: (~r2_hidden(C_64, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_172, c_109])).
% 3.43/1.62  tff(c_198, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_190])).
% 3.43/1.62  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_198])).
% 3.43/1.62  tff(c_204, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.43/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.43/1.62  tff(c_51, plain, (![A_37]: (v1_relat_1(A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.43/1.62  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_51])).
% 3.43/1.62  tff(c_205, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.43/1.62  tff(c_34, plain, (![A_32]: (v1_relat_1(k4_relat_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.43/1.62  tff(c_16, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.43/1.62  tff(c_38, plain, (![A_34]: (k2_relat_1(k4_relat_1(A_34))=k1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.43/1.62  tff(c_274, plain, (![A_80]: (k3_xboole_0(A_80, k2_zfmisc_1(k1_relat_1(A_80), k2_relat_1(A_80)))=A_80 | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.43/1.62  tff(c_1904, plain, (![A_159]: (k3_xboole_0(k4_relat_1(A_159), k2_zfmisc_1(k1_relat_1(k4_relat_1(A_159)), k1_relat_1(A_159)))=k4_relat_1(A_159) | ~v1_relat_1(k4_relat_1(A_159)) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_38, c_274])).
% 3.43/1.62  tff(c_2015, plain, (k3_xboole_0(k4_relat_1(k1_xboole_0), k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)), k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_205, c_1904])).
% 3.43/1.62  tff(c_2026, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_10, c_16, c_2015])).
% 3.43/1.62  tff(c_2078, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2026])).
% 3.43/1.62  tff(c_2081, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2078])).
% 3.43/1.62  tff(c_2085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_2081])).
% 3.43/1.62  tff(c_2086, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2026])).
% 3.43/1.62  tff(c_40, plain, (![A_34]: (k1_relat_1(k4_relat_1(A_34))=k2_relat_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.43/1.62  tff(c_2103, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2086, c_40])).
% 3.43/1.62  tff(c_2121, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_55, c_205, c_2103])).
% 3.43/1.62  tff(c_2123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_2121])).
% 3.43/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.62  
% 3.43/1.62  Inference rules
% 3.43/1.62  ----------------------
% 3.43/1.62  #Ref     : 0
% 3.43/1.62  #Sup     : 531
% 3.43/1.62  #Fact    : 0
% 3.43/1.62  #Define  : 0
% 3.43/1.62  #Split   : 2
% 3.43/1.62  #Chain   : 0
% 3.43/1.62  #Close   : 0
% 3.43/1.62  
% 3.43/1.62  Ordering : KBO
% 3.43/1.62  
% 3.43/1.62  Simplification rules
% 3.43/1.62  ----------------------
% 3.43/1.62  #Subsume      : 226
% 3.43/1.62  #Demod        : 422
% 3.43/1.62  #Tautology    : 92
% 3.43/1.62  #SimpNegUnit  : 13
% 3.43/1.62  #BackRed      : 0
% 3.43/1.62  
% 3.43/1.62  #Partial instantiations: 0
% 3.43/1.62  #Strategies tried      : 1
% 3.43/1.62  
% 3.43/1.62  Timing (in seconds)
% 3.43/1.62  ----------------------
% 3.43/1.62  Preprocessing        : 0.30
% 3.43/1.62  Parsing              : 0.17
% 3.43/1.62  CNF conversion       : 0.02
% 3.43/1.62  Main loop            : 0.53
% 3.43/1.62  Inferencing          : 0.20
% 3.43/1.62  Reduction            : 0.16
% 3.43/1.62  Demodulation         : 0.12
% 3.43/1.62  BG Simplification    : 0.02
% 3.43/1.62  Subsumption          : 0.11
% 3.43/1.62  Abstraction          : 0.03
% 3.43/1.62  MUC search           : 0.00
% 3.43/1.62  Cooper               : 0.00
% 3.43/1.62  Total                : 0.86
% 3.43/1.62  Index Insertion      : 0.00
% 3.43/1.62  Index Deletion       : 0.00
% 3.43/1.62  Index Matching       : 0.00
% 3.43/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
