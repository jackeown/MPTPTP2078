%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  71 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_38,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_45,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_24,B_25] : ~ r2_hidden(A_24,k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_81])).

tff(c_10,plain,(
    ! [A_5] : k1_subset_1(A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_6] : v1_xboole_0(k1_subset_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_61,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33,c_61])).

tff(c_56,plain,(
    ! [A_21] :
      ( v1_funct_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33,c_56])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_1'(A_29,B_30),k1_relat_1(B_30))
      | v5_funct_1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_29)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_100])).

tff(c_105,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_1'(A_29,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_60,c_103])).

tff(c_107,plain,(
    ! [A_31] :
      ( v5_funct_1(k1_xboole_0,A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_105])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_110,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_107,c_28])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:34:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.22  
% 1.72/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.22  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.72/1.22  
% 1.72/1.22  %Foreground sorts:
% 1.72/1.22  
% 1.72/1.22  
% 1.72/1.22  %Background operators:
% 1.72/1.22  
% 1.72/1.22  
% 1.72/1.22  %Foreground operators:
% 1.72/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.72/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.22  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.72/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.72/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.72/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.22  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.72/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.22  
% 1.89/1.23  tff(f_72, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.89/1.23  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.89/1.23  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.89/1.23  tff(f_36, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.89/1.23  tff(f_38, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.89/1.23  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.89/1.23  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.89/1.23  tff(f_45, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.89/1.23  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.89/1.23  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.89/1.23  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.89/1.23  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.23  tff(c_81, plain, (![A_24, B_25]: (~r2_hidden(A_24, k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.23  tff(c_84, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_81])).
% 1.89/1.23  tff(c_10, plain, (![A_5]: (k1_subset_1(A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.89/1.23  tff(c_12, plain, (![A_6]: (v1_xboole_0(k1_subset_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.89/1.23  tff(c_33, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.89/1.23  tff(c_61, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.23  tff(c_65, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_61])).
% 1.89/1.23  tff(c_56, plain, (![A_21]: (v1_funct_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.23  tff(c_60, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_56])).
% 1.89/1.23  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.23  tff(c_100, plain, (![A_29, B_30]: (r2_hidden('#skF_1'(A_29, B_30), k1_relat_1(B_30)) | v5_funct_1(B_30, A_29) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.89/1.23  tff(c_103, plain, (![A_29]: (r2_hidden('#skF_1'(A_29, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_29) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_18, c_100])).
% 1.89/1.23  tff(c_105, plain, (![A_29]: (r2_hidden('#skF_1'(A_29, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_60, c_103])).
% 1.89/1.23  tff(c_107, plain, (![A_31]: (v5_funct_1(k1_xboole_0, A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(negUnitSimplification, [status(thm)], [c_84, c_105])).
% 1.89/1.23  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.89/1.23  tff(c_110, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_107, c_28])).
% 1.89/1.23  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_110])).
% 1.89/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  Inference rules
% 1.89/1.23  ----------------------
% 1.89/1.23  #Ref     : 0
% 1.89/1.23  #Sup     : 20
% 1.89/1.23  #Fact    : 0
% 1.89/1.23  #Define  : 0
% 1.89/1.23  #Split   : 0
% 1.89/1.23  #Chain   : 0
% 1.89/1.23  #Close   : 0
% 1.89/1.23  
% 1.89/1.23  Ordering : KBO
% 1.89/1.23  
% 1.89/1.23  Simplification rules
% 1.89/1.23  ----------------------
% 1.89/1.23  #Subsume      : 1
% 1.89/1.23  #Demod        : 5
% 1.89/1.23  #Tautology    : 14
% 1.89/1.23  #SimpNegUnit  : 1
% 1.89/1.23  #BackRed      : 0
% 1.89/1.23  
% 1.89/1.23  #Partial instantiations: 0
% 1.89/1.23  #Strategies tried      : 1
% 1.89/1.23  
% 1.89/1.23  Timing (in seconds)
% 1.89/1.23  ----------------------
% 1.89/1.23  Preprocessing        : 0.30
% 1.89/1.23  Parsing              : 0.17
% 1.89/1.23  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.12
% 1.89/1.23  Inferencing          : 0.05
% 1.89/1.23  Reduction            : 0.04
% 1.89/1.23  Demodulation         : 0.03
% 1.89/1.24  BG Simplification    : 0.01
% 1.89/1.24  Subsumption          : 0.02
% 1.89/1.24  Abstraction          : 0.00
% 1.89/1.24  MUC search           : 0.00
% 1.89/1.24  Cooper               : 0.00
% 1.89/1.24  Total                : 0.44
% 1.89/1.24  Index Insertion      : 0.00
% 1.89/1.24  Index Deletion       : 0.00
% 1.89/1.24  Index Matching       : 0.00
% 1.89/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
