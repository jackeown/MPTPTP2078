%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:51 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 124 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    v5_funct_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [A_39,B_40] :
      ( k1_funct_1(A_39,B_40) = k1_xboole_0
      | r2_hidden(B_40,k1_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_5,A_39] :
      ( r1_tarski(A_5,k1_relat_1(A_39))
      | k1_funct_1(A_39,'#skF_2'(A_5,k1_relat_1(A_39))) = k1_xboole_0
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_69,c_8])).

tff(c_240,plain,(
    ! [B_74,C_75,A_76] :
      ( r2_hidden(k1_funct_1(B_74,C_75),k1_funct_1(A_76,C_75))
      | ~ r2_hidden(C_75,k1_relat_1(B_74))
      | ~ v5_funct_1(B_74,A_76)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_439,plain,(
    ! [A_109,C_110,B_111] :
      ( ~ v1_xboole_0(k1_funct_1(A_109,C_110))
      | ~ r2_hidden(C_110,k1_relat_1(B_111))
      | ~ v5_funct_1(B_111,A_109)
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_240,c_2])).

tff(c_441,plain,(
    ! [A_5,A_39,B_111] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_5,k1_relat_1(A_39)),k1_relat_1(B_111))
      | ~ v5_funct_1(B_111,A_39)
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39)
      | r1_tarski(A_5,k1_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_439])).

tff(c_540,plain,(
    ! [A_133,A_134,B_135] :
      ( ~ r2_hidden('#skF_2'(A_133,k1_relat_1(A_134)),k1_relat_1(B_135))
      | ~ v5_funct_1(B_135,A_134)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135)
      | r1_tarski(A_133,k1_relat_1(A_134))
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_441])).

tff(c_556,plain,(
    ! [B_136,A_137] :
      ( ~ v5_funct_1(B_136,A_137)
      | ~ v1_funct_1(B_136)
      | ~ v1_relat_1(B_136)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137)
      | r1_tarski(k1_relat_1(B_136),k1_relat_1(A_137)) ) ),
    inference(resolution,[status(thm)],[c_10,c_540])).

tff(c_28,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_590,plain,
    ( ~ v5_funct_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_556,c_28])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.43  
% 2.57/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.43  %$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.57/1.43  
% 2.57/1.43  %Foreground sorts:
% 2.57/1.43  
% 2.57/1.43  
% 2.57/1.43  %Background operators:
% 2.57/1.43  
% 2.57/1.43  
% 2.57/1.43  %Foreground operators:
% 2.57/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.57/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.57/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.57/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.43  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.57/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.57/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.43  
% 2.57/1.44  tff(f_87, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (((v1_relat_1(B) & v1_funct_1(B)) & v5_funct_1(B, A)) => r1_tarski(k1_relat_1(B), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_1)).
% 2.57/1.44  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.57/1.44  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.57/1.44  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.57/1.44  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.57/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.57/1.44  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.44  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.44  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.44  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.44  tff(c_30, plain, (v5_funct_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.44  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.44  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.44  tff(c_69, plain, (![A_39, B_40]: (k1_funct_1(A_39, B_40)=k1_xboole_0 | r2_hidden(B_40, k1_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.57/1.44  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.57/1.44  tff(c_80, plain, (![A_5, A_39]: (r1_tarski(A_5, k1_relat_1(A_39)) | k1_funct_1(A_39, '#skF_2'(A_5, k1_relat_1(A_39)))=k1_xboole_0 | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_69, c_8])).
% 2.57/1.44  tff(c_240, plain, (![B_74, C_75, A_76]: (r2_hidden(k1_funct_1(B_74, C_75), k1_funct_1(A_76, C_75)) | ~r2_hidden(C_75, k1_relat_1(B_74)) | ~v5_funct_1(B_74, A_76) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.44  tff(c_439, plain, (![A_109, C_110, B_111]: (~v1_xboole_0(k1_funct_1(A_109, C_110)) | ~r2_hidden(C_110, k1_relat_1(B_111)) | ~v5_funct_1(B_111, A_109) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_240, c_2])).
% 2.57/1.44  tff(c_441, plain, (![A_5, A_39, B_111]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden('#skF_2'(A_5, k1_relat_1(A_39)), k1_relat_1(B_111)) | ~v5_funct_1(B_111, A_39) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39) | r1_tarski(A_5, k1_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_80, c_439])).
% 2.57/1.44  tff(c_540, plain, (![A_133, A_134, B_135]: (~r2_hidden('#skF_2'(A_133, k1_relat_1(A_134)), k1_relat_1(B_135)) | ~v5_funct_1(B_135, A_134) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135) | r1_tarski(A_133, k1_relat_1(A_134)) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_441])).
% 2.57/1.44  tff(c_556, plain, (![B_136, A_137]: (~v5_funct_1(B_136, A_137) | ~v1_funct_1(B_136) | ~v1_relat_1(B_136) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137) | r1_tarski(k1_relat_1(B_136), k1_relat_1(A_137)))), inference(resolution, [status(thm)], [c_10, c_540])).
% 2.57/1.44  tff(c_28, plain, (~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.44  tff(c_590, plain, (~v5_funct_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_556, c_28])).
% 2.57/1.44  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_590])).
% 2.57/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  Inference rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Ref     : 0
% 2.57/1.44  #Sup     : 134
% 2.57/1.44  #Fact    : 0
% 2.57/1.44  #Define  : 0
% 2.57/1.44  #Split   : 1
% 2.57/1.44  #Chain   : 0
% 2.57/1.44  #Close   : 0
% 2.57/1.44  
% 2.57/1.44  Ordering : KBO
% 2.57/1.44  
% 2.57/1.44  Simplification rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Subsume      : 54
% 2.57/1.44  #Demod        : 10
% 2.57/1.44  #Tautology    : 10
% 2.57/1.44  #SimpNegUnit  : 0
% 2.57/1.44  #BackRed      : 0
% 2.57/1.44  
% 2.57/1.44  #Partial instantiations: 0
% 2.57/1.44  #Strategies tried      : 1
% 2.57/1.44  
% 2.57/1.44  Timing (in seconds)
% 2.57/1.44  ----------------------
% 2.57/1.45  Preprocessing        : 0.27
% 2.57/1.45  Parsing              : 0.14
% 2.57/1.45  CNF conversion       : 0.02
% 2.57/1.45  Main loop            : 0.36
% 2.57/1.45  Inferencing          : 0.14
% 2.57/1.45  Reduction            : 0.08
% 2.57/1.45  Demodulation         : 0.05
% 2.57/1.45  BG Simplification    : 0.02
% 2.57/1.45  Subsumption          : 0.10
% 2.57/1.45  Abstraction          : 0.02
% 2.57/1.45  MUC search           : 0.00
% 2.57/1.45  Cooper               : 0.00
% 2.57/1.45  Total                : 0.66
% 2.57/1.45  Index Insertion      : 0.00
% 2.57/1.45  Index Deletion       : 0.00
% 2.57/1.45  Index Matching       : 0.00
% 2.57/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
