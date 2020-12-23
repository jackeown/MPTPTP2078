%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:51 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 124 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B)
              & v5_funct_1(B,A) )
           => r1_tarski(k1_relat_1(B),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    v5_funct_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_39,B_40] :
      ( k1_funct_1(A_39,B_40) = k1_xboole_0
      | r2_hidden(B_40,k1_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_1,A_39] :
      ( r1_tarski(A_1,k1_relat_1(A_39))
      | k1_funct_1(A_39,'#skF_1'(A_1,k1_relat_1(A_39))) = k1_xboole_0
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_72,c_4])).

tff(c_288,plain,(
    ! [B_89,C_90,A_91] :
      ( r2_hidden(k1_funct_1(B_89,C_90),k1_funct_1(A_91,C_90))
      | ~ r2_hidden(C_90,k1_relat_1(B_89))
      | ~ v5_funct_1(B_89,A_91)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_324,plain,(
    ! [A_95,C_96,B_97] :
      ( ~ v1_xboole_0(k1_funct_1(A_95,C_96))
      | ~ r2_hidden(C_96,k1_relat_1(B_97))
      | ~ v5_funct_1(B_97,A_95)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_288,c_10])).

tff(c_326,plain,(
    ! [A_1,A_39,B_97] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1,k1_relat_1(A_39)),k1_relat_1(B_97))
      | ~ v5_funct_1(B_97,A_39)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | r1_tarski(A_1,k1_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_324])).

tff(c_434,plain,(
    ! [A_124,A_125,B_126] :
      ( ~ r2_hidden('#skF_1'(A_124,k1_relat_1(A_125)),k1_relat_1(B_126))
      | ~ v5_funct_1(B_126,A_125)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | r1_tarski(A_124,k1_relat_1(A_125))
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_326])).

tff(c_450,plain,(
    ! [B_127,A_128] :
      ( ~ v5_funct_1(B_127,A_128)
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128)
      | r1_tarski(k1_relat_1(B_127),k1_relat_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_6,c_434])).

tff(c_26,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_476,plain,
    ( ~ v5_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_450,c_26])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.55  
% 2.85/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.55  %$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.85/1.55  
% 2.85/1.55  %Foreground sorts:
% 2.85/1.55  
% 2.85/1.55  
% 2.85/1.55  %Background operators:
% 2.85/1.55  
% 2.85/1.55  
% 2.85/1.55  %Foreground operators:
% 2.85/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.85/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.55  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.85/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.85/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.55  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.55  
% 2.85/1.56  tff(f_86, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (((v1_relat_1(B) & v1_funct_1(B)) & v5_funct_1(B, A)) => r1_tarski(k1_relat_1(B), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_1)).
% 2.85/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.85/1.56  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/1.56  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.85/1.56  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.85/1.56  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.85/1.56  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.56  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.56  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.56  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.56  tff(c_28, plain, (v5_funct_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.56  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.56  tff(c_72, plain, (![A_39, B_40]: (k1_funct_1(A_39, B_40)=k1_xboole_0 | r2_hidden(B_40, k1_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.85/1.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.56  tff(c_83, plain, (![A_1, A_39]: (r1_tarski(A_1, k1_relat_1(A_39)) | k1_funct_1(A_39, '#skF_1'(A_1, k1_relat_1(A_39)))=k1_xboole_0 | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_72, c_4])).
% 2.85/1.56  tff(c_288, plain, (![B_89, C_90, A_91]: (r2_hidden(k1_funct_1(B_89, C_90), k1_funct_1(A_91, C_90)) | ~r2_hidden(C_90, k1_relat_1(B_89)) | ~v5_funct_1(B_89, A_91) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/1.56  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.56  tff(c_324, plain, (![A_95, C_96, B_97]: (~v1_xboole_0(k1_funct_1(A_95, C_96)) | ~r2_hidden(C_96, k1_relat_1(B_97)) | ~v5_funct_1(B_97, A_95) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_288, c_10])).
% 2.85/1.56  tff(c_326, plain, (![A_1, A_39, B_97]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden('#skF_1'(A_1, k1_relat_1(A_39)), k1_relat_1(B_97)) | ~v5_funct_1(B_97, A_39) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | r1_tarski(A_1, k1_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_83, c_324])).
% 2.85/1.56  tff(c_434, plain, (![A_124, A_125, B_126]: (~r2_hidden('#skF_1'(A_124, k1_relat_1(A_125)), k1_relat_1(B_126)) | ~v5_funct_1(B_126, A_125) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | r1_tarski(A_124, k1_relat_1(A_125)) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_326])).
% 2.85/1.56  tff(c_450, plain, (![B_127, A_128]: (~v5_funct_1(B_127, A_128) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128) | r1_tarski(k1_relat_1(B_127), k1_relat_1(A_128)))), inference(resolution, [status(thm)], [c_6, c_434])).
% 2.85/1.56  tff(c_26, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.56  tff(c_476, plain, (~v5_funct_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_450, c_26])).
% 2.85/1.56  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_476])).
% 2.85/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.56  
% 2.85/1.56  Inference rules
% 2.85/1.56  ----------------------
% 2.85/1.56  #Ref     : 0
% 2.85/1.56  #Sup     : 109
% 2.85/1.56  #Fact    : 0
% 2.85/1.56  #Define  : 0
% 2.85/1.56  #Split   : 1
% 2.85/1.56  #Chain   : 0
% 2.85/1.56  #Close   : 0
% 2.85/1.56  
% 2.85/1.56  Ordering : KBO
% 2.85/1.57  
% 2.85/1.57  Simplification rules
% 2.85/1.57  ----------------------
% 2.85/1.57  #Subsume      : 43
% 2.85/1.57  #Demod        : 8
% 2.85/1.57  #Tautology    : 5
% 2.85/1.57  #SimpNegUnit  : 0
% 2.85/1.57  #BackRed      : 0
% 2.85/1.57  
% 2.85/1.57  #Partial instantiations: 0
% 2.85/1.57  #Strategies tried      : 1
% 2.85/1.57  
% 2.85/1.57  Timing (in seconds)
% 2.85/1.57  ----------------------
% 2.85/1.57  Preprocessing        : 0.36
% 2.85/1.57  Parsing              : 0.19
% 2.85/1.57  CNF conversion       : 0.03
% 2.85/1.57  Main loop            : 0.35
% 2.85/1.57  Inferencing          : 0.13
% 2.85/1.57  Reduction            : 0.08
% 2.85/1.57  Demodulation         : 0.05
% 2.85/1.57  BG Simplification    : 0.02
% 2.85/1.57  Subsumption          : 0.09
% 2.85/1.57  Abstraction          : 0.02
% 2.85/1.57  MUC search           : 0.00
% 2.85/1.57  Cooper               : 0.00
% 2.85/1.57  Total                : 0.74
% 2.85/1.57  Index Insertion      : 0.00
% 2.85/1.57  Index Deletion       : 0.00
% 2.85/1.57  Index Matching       : 0.00
% 2.85/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
