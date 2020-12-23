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
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   87 ( 233 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B)
          & v5_ordinal1(B) )
       => ! [C] :
            ( v3_ordinal1(C)
           => ( v1_relat_1(k7_relat_1(B,C))
              & v5_relat_1(k7_relat_1(B,C),A)
              & v1_funct_1(k7_relat_1(B,C))
              & v5_ordinal1(k7_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_relat_1(C) )
     => ( v1_relat_1(k5_relat_1(C,B))
        & v5_relat_1(k5_relat_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc25_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v5_ordinal1(A)
        & v3_ordinal1(B) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v5_relat_1(k7_relat_1(A,B),k2_relat_1(A))
        & v5_ordinal1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( v1_funct_1(k7_relat_1(A_10,B_11))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_relat_1(A_1),B_2) = k7_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [C_45,B_46,A_47] :
      ( v5_relat_1(k5_relat_1(C_45,B_46),A_47)
      | ~ v1_relat_1(C_45)
      | ~ v5_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [B_2,A_1,A_47] :
      ( v5_relat_1(k7_relat_1(B_2,A_1),A_47)
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v5_relat_1(B_2,A_47)
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_130,plain,(
    ! [B_48,A_49,A_50] :
      ( v5_relat_1(k7_relat_1(B_48,A_49),A_50)
      | ~ v5_relat_1(B_48,A_50)
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_126])).

tff(c_36,plain,(
    v5_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_100,plain,(
    ! [A_38,B_39] :
      ( v5_ordinal1(k7_relat_1(A_38,B_39))
      | ~ v3_ordinal1(B_39)
      | ~ v5_ordinal1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,
    ( ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_53,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_48])).

tff(c_57,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_53])).

tff(c_58,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_89,plain,(
    ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_103,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v5_ordinal1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_89])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_34,c_103])).

tff(c_108,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_120,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_133,plain,
    ( ~ v5_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_120])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_133])).

tff(c_140,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_144,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_140])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:50:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.23  
% 2.23/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.24  %$ v5_relat_1 > v4_relat_1 > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.24  
% 2.23/1.24  %Foreground sorts:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Background operators:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Foreground operators:
% 2.23/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.24  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 2.23/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.24  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.23/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.24  
% 2.23/1.25  tff(f_103, negated_conjecture, ~(![A, B]: ((((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)) => (![C]: (v3_ordinal1(C) => (((v1_relat_1(k7_relat_1(B, C)) & v5_relat_1(k7_relat_1(B, C), A)) & v1_funct_1(k7_relat_1(B, C))) & v5_ordinal1(k7_relat_1(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_ordinal1)).
% 2.23/1.25  tff(f_69, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.23/1.25  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.23/1.25  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.23/1.25  tff(f_45, axiom, (![A, B, C]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_relat_1(C)) => (v1_relat_1(k5_relat_1(C, B)) & v5_relat_1(k5_relat_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc25_relat_1)).
% 2.23/1.25  tff(f_83, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v5_ordinal1(A)) & v3_ordinal1(B)) => ((v1_relat_1(k7_relat_1(A, B)) & v5_relat_1(k7_relat_1(A, B), k2_relat_1(A))) & v5_ordinal1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_ordinal1)).
% 2.23/1.25  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.23/1.25  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.23/1.25  tff(c_22, plain, (![A_10, B_11]: (v1_funct_1(k7_relat_1(A_10, B_11)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.23/1.25  tff(c_40, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.23/1.25  tff(c_18, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.25  tff(c_2, plain, (![A_1, B_2]: (k5_relat_1(k6_relat_1(A_1), B_2)=k7_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.25  tff(c_121, plain, (![C_45, B_46, A_47]: (v5_relat_1(k5_relat_1(C_45, B_46), A_47) | ~v1_relat_1(C_45) | ~v5_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.25  tff(c_126, plain, (![B_2, A_1, A_47]: (v5_relat_1(k7_relat_1(B_2, A_1), A_47) | ~v1_relat_1(k6_relat_1(A_1)) | ~v5_relat_1(B_2, A_47) | ~v1_relat_1(B_2) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_121])).
% 2.23/1.25  tff(c_130, plain, (![B_48, A_49, A_50]: (v5_relat_1(k7_relat_1(B_48, A_49), A_50) | ~v5_relat_1(B_48, A_50) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_126])).
% 2.23/1.25  tff(c_36, plain, (v5_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.23/1.25  tff(c_34, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.23/1.25  tff(c_100, plain, (![A_38, B_39]: (v5_ordinal1(k7_relat_1(A_38, B_39)) | ~v3_ordinal1(B_39) | ~v5_ordinal1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.25  tff(c_50, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.23/1.25  tff(c_32, plain, (~v5_ordinal1(k7_relat_1('#skF_2', '#skF_3')) | ~v1_funct_1(k7_relat_1('#skF_2', '#skF_3')) | ~v5_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.23/1.25  tff(c_48, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.23/1.25  tff(c_53, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_48])).
% 2.23/1.25  tff(c_57, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_53])).
% 2.23/1.25  tff(c_58, plain, (~v5_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_1') | ~v1_funct_1(k7_relat_1('#skF_2', '#skF_3')) | ~v5_ordinal1(k7_relat_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.23/1.25  tff(c_89, plain, (~v5_ordinal1(k7_relat_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 2.23/1.25  tff(c_103, plain, (~v3_ordinal1('#skF_3') | ~v5_ordinal1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_100, c_89])).
% 2.23/1.25  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_34, c_103])).
% 2.23/1.25  tff(c_108, plain, (~v1_funct_1(k7_relat_1('#skF_2', '#skF_3')) | ~v5_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 2.23/1.25  tff(c_120, plain, (~v5_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_108])).
% 2.23/1.25  tff(c_133, plain, (~v5_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_130, c_120])).
% 2.23/1.25  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_133])).
% 2.23/1.25  tff(c_140, plain, (~v1_funct_1(k7_relat_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_108])).
% 2.23/1.25  tff(c_144, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_140])).
% 2.23/1.25  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_144])).
% 2.23/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  Inference rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Ref     : 0
% 2.23/1.25  #Sup     : 14
% 2.23/1.25  #Fact    : 0
% 2.23/1.25  #Define  : 0
% 2.23/1.25  #Split   : 3
% 2.23/1.25  #Chain   : 0
% 2.23/1.25  #Close   : 0
% 2.23/1.25  
% 2.23/1.25  Ordering : KBO
% 2.23/1.25  
% 2.23/1.25  Simplification rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Subsume      : 1
% 2.23/1.25  #Demod        : 22
% 2.23/1.25  #Tautology    : 5
% 2.23/1.25  #SimpNegUnit  : 0
% 2.23/1.25  #BackRed      : 0
% 2.23/1.25  
% 2.23/1.25  #Partial instantiations: 0
% 2.23/1.25  #Strategies tried      : 1
% 2.23/1.25  
% 2.23/1.25  Timing (in seconds)
% 2.23/1.25  ----------------------
% 2.23/1.26  Preprocessing        : 0.28
% 2.23/1.26  Parsing              : 0.15
% 2.23/1.26  CNF conversion       : 0.02
% 2.23/1.26  Main loop            : 0.16
% 2.23/1.26  Inferencing          : 0.06
% 2.23/1.26  Reduction            : 0.05
% 2.23/1.26  Demodulation         : 0.04
% 2.23/1.26  BG Simplification    : 0.01
% 2.23/1.26  Subsumption          : 0.03
% 2.23/1.26  Abstraction          : 0.01
% 2.23/1.26  MUC search           : 0.00
% 2.23/1.26  Cooper               : 0.00
% 2.23/1.26  Total                : 0.48
% 2.23/1.26  Index Insertion      : 0.00
% 2.23/1.26  Index Deletion       : 0.00
% 2.23/1.26  Index Matching       : 0.00
% 2.23/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
