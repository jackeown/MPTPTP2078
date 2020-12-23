%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 120 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B)
              & v5_funct_1(B,A) )
           => r1_tarski(k1_relat_1(B),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_55,axiom,(
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

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    v5_funct_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_45,plain,(
    ! [A_31,C_32,B_33] :
      ( ~ r2_hidden(A_31,C_32)
      | ~ r1_xboole_0(k2_tarski(A_31,B_33),C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_77,plain,(
    ! [A_43,B_44] :
      ( k1_funct_1(A_43,B_44) = k1_xboole_0
      | r2_hidden(B_44,k1_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_1,A_43] :
      ( r1_tarski(A_1,k1_relat_1(A_43))
      | k1_funct_1(A_43,'#skF_1'(A_1,k1_relat_1(A_43))) = k1_xboole_0
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_201,plain,(
    ! [B_72,C_73,A_74] :
      ( r2_hidden(k1_funct_1(B_72,C_73),k1_funct_1(A_74,C_73))
      | ~ r2_hidden(C_73,k1_relat_1(B_72))
      | ~ v5_funct_1(B_72,A_74)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_213,plain,(
    ! [B_72,A_1,A_43] :
      ( r2_hidden(k1_funct_1(B_72,'#skF_1'(A_1,k1_relat_1(A_43))),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1,k1_relat_1(A_43)),k1_relat_1(B_72))
      | ~ v5_funct_1(B_72,A_43)
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43)
      | r1_tarski(A_1,k1_relat_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_201])).

tff(c_486,plain,(
    ! [A_125,A_126,B_127] :
      ( ~ r2_hidden('#skF_1'(A_125,k1_relat_1(A_126)),k1_relat_1(B_127))
      | ~ v5_funct_1(B_127,A_126)
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126)
      | r1_tarski(A_125,k1_relat_1(A_126))
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_213])).

tff(c_502,plain,(
    ! [B_128,A_129] :
      ( ~ v5_funct_1(B_128,A_129)
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129)
      | r1_tarski(k1_relat_1(B_128),k1_relat_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_6,c_486])).

tff(c_26,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_524,plain,
    ( ~ v5_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_502,c_26])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.44  
% 2.66/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.45  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.66/1.45  
% 2.66/1.45  %Foreground sorts:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Background operators:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Foreground operators:
% 2.66/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.66/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.45  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.66/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.45  
% 2.81/1.46  tff(f_87, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (((v1_relat_1(B) & v1_funct_1(B)) & v5_funct_1(B, A)) => r1_tarski(k1_relat_1(B), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_1)).
% 2.81/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.46  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.81/1.46  tff(f_39, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.81/1.46  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.81/1.46  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.81/1.46  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.81/1.46  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.81/1.46  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.81/1.46  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.81/1.46  tff(c_28, plain, (v5_funct_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.81/1.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.46  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.81/1.46  tff(c_45, plain, (![A_31, C_32, B_33]: (~r2_hidden(A_31, C_32) | ~r1_xboole_0(k2_tarski(A_31, B_33), C_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.46  tff(c_50, plain, (![A_31]: (~r2_hidden(A_31, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_45])).
% 2.81/1.46  tff(c_77, plain, (![A_43, B_44]: (k1_funct_1(A_43, B_44)=k1_xboole_0 | r2_hidden(B_44, k1_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.46  tff(c_85, plain, (![A_1, A_43]: (r1_tarski(A_1, k1_relat_1(A_43)) | k1_funct_1(A_43, '#skF_1'(A_1, k1_relat_1(A_43)))=k1_xboole_0 | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_77, c_4])).
% 2.81/1.46  tff(c_201, plain, (![B_72, C_73, A_74]: (r2_hidden(k1_funct_1(B_72, C_73), k1_funct_1(A_74, C_73)) | ~r2_hidden(C_73, k1_relat_1(B_72)) | ~v5_funct_1(B_72, A_74) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.81/1.46  tff(c_213, plain, (![B_72, A_1, A_43]: (r2_hidden(k1_funct_1(B_72, '#skF_1'(A_1, k1_relat_1(A_43))), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1, k1_relat_1(A_43)), k1_relat_1(B_72)) | ~v5_funct_1(B_72, A_43) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43) | r1_tarski(A_1, k1_relat_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_85, c_201])).
% 2.81/1.46  tff(c_486, plain, (![A_125, A_126, B_127]: (~r2_hidden('#skF_1'(A_125, k1_relat_1(A_126)), k1_relat_1(B_127)) | ~v5_funct_1(B_127, A_126) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126) | r1_tarski(A_125, k1_relat_1(A_126)) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(negUnitSimplification, [status(thm)], [c_50, c_213])).
% 2.81/1.46  tff(c_502, plain, (![B_128, A_129]: (~v5_funct_1(B_128, A_129) | ~v1_funct_1(B_128) | ~v1_relat_1(B_128) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129) | r1_tarski(k1_relat_1(B_128), k1_relat_1(A_129)))), inference(resolution, [status(thm)], [c_6, c_486])).
% 2.81/1.46  tff(c_26, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.81/1.46  tff(c_524, plain, (~v5_funct_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_502, c_26])).
% 2.81/1.46  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_524])).
% 2.81/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.46  
% 2.81/1.46  Inference rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Ref     : 0
% 2.81/1.46  #Sup     : 115
% 2.81/1.46  #Fact    : 0
% 2.81/1.46  #Define  : 0
% 2.81/1.46  #Split   : 1
% 2.81/1.46  #Chain   : 0
% 2.81/1.46  #Close   : 0
% 2.81/1.46  
% 2.81/1.46  Ordering : KBO
% 2.81/1.46  
% 2.81/1.46  Simplification rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Subsume      : 37
% 2.81/1.46  #Demod        : 12
% 2.81/1.46  #Tautology    : 10
% 2.81/1.46  #SimpNegUnit  : 1
% 2.81/1.46  #BackRed      : 0
% 2.81/1.46  
% 2.81/1.46  #Partial instantiations: 0
% 2.81/1.46  #Strategies tried      : 1
% 2.81/1.46  
% 2.81/1.46  Timing (in seconds)
% 2.81/1.46  ----------------------
% 2.81/1.46  Preprocessing        : 0.29
% 2.81/1.46  Parsing              : 0.15
% 2.81/1.46  CNF conversion       : 0.02
% 2.81/1.46  Main loop            : 0.36
% 2.81/1.46  Inferencing          : 0.13
% 2.81/1.46  Reduction            : 0.08
% 2.81/1.46  Demodulation         : 0.06
% 2.81/1.46  BG Simplification    : 0.02
% 2.81/1.46  Subsumption          : 0.10
% 2.81/1.46  Abstraction          : 0.02
% 2.81/1.46  MUC search           : 0.00
% 2.81/1.46  Cooper               : 0.00
% 2.81/1.46  Total                : 0.67
% 2.81/1.46  Index Insertion      : 0.00
% 2.81/1.46  Index Deletion       : 0.00
% 2.81/1.46  Index Matching       : 0.00
% 2.81/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
