%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:38 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  51 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_59,plain,(
    ! [A_62] : k2_zfmisc_1(A_62,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_55,B_56] : v1_relat_1(k2_zfmisc_1(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_38])).

tff(c_679,plain,(
    ! [A_130,B_131,C_132] :
      ( r2_hidden(k4_tarski('#skF_3'(A_130,B_131,C_132),'#skF_2'(A_130,B_131,C_132)),A_130)
      | r2_hidden('#skF_4'(A_130,B_131,C_132),C_132)
      | k9_relat_1(A_130,B_131) = C_132
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_6,C_66] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_91,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_709,plain,(
    ! [B_131,C_132] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_131,C_132),C_132)
      | k9_relat_1(k1_xboole_0,B_131) = C_132
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_679,c_91])).

tff(c_925,plain,(
    ! [B_143,C_144] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_143,C_144),C_144)
      | k9_relat_1(k1_xboole_0,B_143) = C_144 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_709])).

tff(c_967,plain,(
    ! [B_143] : k9_relat_1(k1_xboole_0,B_143) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_925,c_91])).

tff(c_40,plain,(
    k9_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.31  % Computer   : n022.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 09:19:26 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 2.55/1.34  
% 2.55/1.34  %Foreground sorts:
% 2.55/1.34  
% 2.55/1.34  
% 2.55/1.34  %Background operators:
% 2.55/1.34  
% 2.55/1.34  
% 2.55/1.34  %Foreground operators:
% 2.55/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.55/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.55/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.55/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.55/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.55/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.55/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.34  
% 2.55/1.35  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.55/1.35  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.55/1.35  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 2.55/1.35  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.55/1.35  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.55/1.35  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.55/1.35  tff(f_71, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.55/1.35  tff(c_59, plain, (![A_62]: (k2_zfmisc_1(A_62, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.35  tff(c_38, plain, (![A_55, B_56]: (v1_relat_1(k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.55/1.35  tff(c_63, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59, c_38])).
% 2.55/1.35  tff(c_679, plain, (![A_130, B_131, C_132]: (r2_hidden(k4_tarski('#skF_3'(A_130, B_131, C_132), '#skF_2'(A_130, B_131, C_132)), A_130) | r2_hidden('#skF_4'(A_130, B_131, C_132), C_132) | k9_relat_1(A_130, B_131)=C_132 | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.55/1.35  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.35  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.55/1.35  tff(c_86, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.35  tff(c_89, plain, (![A_6, C_66]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_86])).
% 2.55/1.35  tff(c_91, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 2.55/1.35  tff(c_709, plain, (![B_131, C_132]: (r2_hidden('#skF_4'(k1_xboole_0, B_131, C_132), C_132) | k9_relat_1(k1_xboole_0, B_131)=C_132 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_679, c_91])).
% 2.55/1.35  tff(c_925, plain, (![B_143, C_144]: (r2_hidden('#skF_4'(k1_xboole_0, B_143, C_144), C_144) | k9_relat_1(k1_xboole_0, B_143)=C_144)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_709])).
% 2.55/1.35  tff(c_967, plain, (![B_143]: (k9_relat_1(k1_xboole_0, B_143)=k1_xboole_0)), inference(resolution, [status(thm)], [c_925, c_91])).
% 2.55/1.35  tff(c_40, plain, (k9_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.35  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_967, c_40])).
% 2.55/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.35  
% 2.55/1.35  Inference rules
% 2.55/1.35  ----------------------
% 2.55/1.35  #Ref     : 0
% 2.55/1.35  #Sup     : 202
% 2.55/1.35  #Fact    : 0
% 2.55/1.35  #Define  : 0
% 2.55/1.35  #Split   : 0
% 2.55/1.35  #Chain   : 0
% 2.55/1.35  #Close   : 0
% 2.55/1.35  
% 2.55/1.35  Ordering : KBO
% 2.55/1.35  
% 2.55/1.35  Simplification rules
% 2.55/1.35  ----------------------
% 2.55/1.35  #Subsume      : 44
% 2.55/1.35  #Demod        : 107
% 2.55/1.35  #Tautology    : 69
% 2.55/1.35  #SimpNegUnit  : 5
% 2.55/1.35  #BackRed      : 8
% 2.55/1.35  
% 2.55/1.35  #Partial instantiations: 0
% 2.55/1.35  #Strategies tried      : 1
% 2.55/1.35  
% 2.55/1.35  Timing (in seconds)
% 2.55/1.35  ----------------------
% 2.55/1.36  Preprocessing        : 0.28
% 2.55/1.36  Parsing              : 0.15
% 2.55/1.36  CNF conversion       : 0.02
% 2.55/1.36  Main loop            : 0.33
% 2.55/1.36  Inferencing          : 0.14
% 2.55/1.36  Reduction            : 0.09
% 2.55/1.36  Demodulation         : 0.07
% 2.55/1.36  BG Simplification    : 0.02
% 2.55/1.36  Subsumption          : 0.06
% 2.55/1.36  Abstraction          : 0.02
% 2.55/1.36  MUC search           : 0.00
% 2.55/1.36  Cooper               : 0.00
% 2.55/1.36  Total                : 0.64
% 2.55/1.36  Index Insertion      : 0.00
% 2.55/1.36  Index Deletion       : 0.00
% 2.55/1.36  Index Matching       : 0.00
% 2.55/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
