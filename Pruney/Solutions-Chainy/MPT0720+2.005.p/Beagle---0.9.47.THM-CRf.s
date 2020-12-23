%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 120 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

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

tff(c_38,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | ~ r1_xboole_0(k1_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_77,plain,(
    ! [A_41,B_42] :
      ( k1_funct_1(A_41,B_42) = k1_xboole_0
      | r2_hidden(B_42,k1_relat_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_1,A_41] :
      ( r1_tarski(A_1,k1_relat_1(A_41))
      | k1_funct_1(A_41,'#skF_1'(A_1,k1_relat_1(A_41))) = k1_xboole_0
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_146,plain,(
    ! [B_61,C_62,A_63] :
      ( r2_hidden(k1_funct_1(B_61,C_62),k1_funct_1(A_63,C_62))
      | ~ r2_hidden(C_62,k1_relat_1(B_61))
      | ~ v5_funct_1(B_61,A_63)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [B_61,A_1,A_41] :
      ( r2_hidden(k1_funct_1(B_61,'#skF_1'(A_1,k1_relat_1(A_41))),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1,k1_relat_1(A_41)),k1_relat_1(B_61))
      | ~ v5_funct_1(B_61,A_41)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41)
      | r1_tarski(A_1,k1_relat_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_146])).

tff(c_486,plain,(
    ! [A_123,A_124,B_125] :
      ( ~ r2_hidden('#skF_1'(A_123,k1_relat_1(A_124)),k1_relat_1(B_125))
      | ~ v5_funct_1(B_125,A_124)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124)
      | r1_tarski(A_123,k1_relat_1(A_124))
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_154])).

tff(c_502,plain,(
    ! [B_126,A_127] :
      ( ~ v5_funct_1(B_126,A_127)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127)
      | r1_tarski(k1_relat_1(B_126),k1_relat_1(A_127)) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.88/1.41  
% 2.88/1.41  %Foreground sorts:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Background operators:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Foreground operators:
% 2.88/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.88/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.41  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.88/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.88/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.41  
% 2.88/1.42  tff(f_87, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (((v1_relat_1(B) & v1_funct_1(B)) & v5_funct_1(B, A)) => r1_tarski(k1_relat_1(B), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_1)).
% 2.88/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.88/1.42  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.88/1.42  tff(f_39, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.88/1.42  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.88/1.42  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.88/1.42  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.42  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.42  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.42  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.42  tff(c_28, plain, (v5_funct_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.42  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.88/1.42  tff(c_38, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | ~r1_xboole_0(k1_tarski(A_26), B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.42  tff(c_43, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_38])).
% 2.88/1.42  tff(c_77, plain, (![A_41, B_42]: (k1_funct_1(A_41, B_42)=k1_xboole_0 | r2_hidden(B_42, k1_relat_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.88/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.42  tff(c_85, plain, (![A_1, A_41]: (r1_tarski(A_1, k1_relat_1(A_41)) | k1_funct_1(A_41, '#skF_1'(A_1, k1_relat_1(A_41)))=k1_xboole_0 | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_77, c_4])).
% 2.88/1.42  tff(c_146, plain, (![B_61, C_62, A_63]: (r2_hidden(k1_funct_1(B_61, C_62), k1_funct_1(A_63, C_62)) | ~r2_hidden(C_62, k1_relat_1(B_61)) | ~v5_funct_1(B_61, A_63) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.42  tff(c_154, plain, (![B_61, A_1, A_41]: (r2_hidden(k1_funct_1(B_61, '#skF_1'(A_1, k1_relat_1(A_41))), k1_xboole_0) | ~r2_hidden('#skF_1'(A_1, k1_relat_1(A_41)), k1_relat_1(B_61)) | ~v5_funct_1(B_61, A_41) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41) | r1_tarski(A_1, k1_relat_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_85, c_146])).
% 2.88/1.42  tff(c_486, plain, (![A_123, A_124, B_125]: (~r2_hidden('#skF_1'(A_123, k1_relat_1(A_124)), k1_relat_1(B_125)) | ~v5_funct_1(B_125, A_124) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124) | r1_tarski(A_123, k1_relat_1(A_124)) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(negUnitSimplification, [status(thm)], [c_43, c_154])).
% 2.88/1.42  tff(c_502, plain, (![B_126, A_127]: (~v5_funct_1(B_126, A_127) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127) | r1_tarski(k1_relat_1(B_126), k1_relat_1(A_127)))), inference(resolution, [status(thm)], [c_6, c_486])).
% 2.88/1.42  tff(c_26, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.88/1.42  tff(c_524, plain, (~v5_funct_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_502, c_26])).
% 2.88/1.42  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_524])).
% 2.88/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.42  
% 2.88/1.42  Inference rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Ref     : 0
% 2.88/1.42  #Sup     : 115
% 2.88/1.42  #Fact    : 0
% 2.88/1.42  #Define  : 0
% 2.88/1.42  #Split   : 1
% 2.88/1.42  #Chain   : 0
% 2.88/1.42  #Close   : 0
% 2.88/1.42  
% 2.88/1.42  Ordering : KBO
% 2.88/1.42  
% 2.88/1.42  Simplification rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Subsume      : 37
% 2.88/1.42  #Demod        : 12
% 2.88/1.42  #Tautology    : 10
% 2.88/1.42  #SimpNegUnit  : 1
% 2.88/1.42  #BackRed      : 0
% 2.88/1.42  
% 2.88/1.42  #Partial instantiations: 0
% 2.88/1.42  #Strategies tried      : 1
% 2.88/1.42  
% 2.88/1.42  Timing (in seconds)
% 2.88/1.42  ----------------------
% 2.88/1.42  Preprocessing        : 0.29
% 2.88/1.42  Parsing              : 0.16
% 2.88/1.42  CNF conversion       : 0.02
% 2.88/1.42  Main loop            : 0.37
% 2.88/1.42  Inferencing          : 0.14
% 2.88/1.42  Reduction            : 0.09
% 2.88/1.42  Demodulation         : 0.06
% 2.88/1.42  BG Simplification    : 0.02
% 2.88/1.42  Subsumption          : 0.10
% 2.88/1.43  Abstraction          : 0.02
% 2.88/1.43  MUC search           : 0.00
% 2.88/1.43  Cooper               : 0.00
% 2.88/1.43  Total                : 0.69
% 2.88/1.43  Index Insertion      : 0.00
% 2.88/1.43  Index Deletion       : 0.00
% 2.88/1.43  Index Matching       : 0.00
% 2.88/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
