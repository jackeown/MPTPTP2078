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
% DateTime   : Thu Dec  3 10:05:52 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 106 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 285 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
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

tff(f_63,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    v5_funct_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_90,plain,(
    ! [A_50,B_51] :
      ( k1_funct_1(A_50,B_51) = k1_xboole_0
      | r2_hidden(B_51,k1_relat_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_1,A_50] :
      ( r1_tarski(A_1,k1_relat_1(A_50))
      | k1_funct_1(A_50,'#skF_1'(A_1,k1_relat_1(A_50))) = k1_xboole_0
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_90,c_4])).

tff(c_307,plain,(
    ! [B_95,C_96,A_97] :
      ( r2_hidden(k1_funct_1(B_95,C_96),k1_funct_1(A_97,C_96))
      | ~ r2_hidden(C_96,k1_relat_1(B_95))
      | ~ v5_funct_1(B_95,A_97)
      | ~ v1_funct_1(B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_44,B_45,B_46] :
      ( r2_hidden('#skF_2'(A_44,B_45),B_46)
      | ~ r1_tarski(B_45,B_46)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_63,B_64,B_65,B_66] :
      ( r2_hidden('#skF_2'(A_63,B_64),B_65)
      | ~ r1_tarski(B_66,B_65)
      | ~ r1_tarski(B_64,B_66)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_146,plain,(
    ! [A_63,B_64,A_6] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_6)
      | ~ r1_tarski(B_64,k1_xboole_0)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_8,c_140])).

tff(c_147,plain,(
    ! [A_67,B_68,A_69] :
      ( r2_hidden('#skF_2'(A_67,B_68),A_69)
      | ~ r1_tarski(B_68,k1_xboole_0)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_140])).

tff(c_10,plain,(
    ! [D_13,A_7,B_8] :
      ( ~ r2_hidden(D_13,'#skF_2'(A_7,B_8))
      | ~ r2_hidden(D_13,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_156,plain,(
    ! [A_70,B_71,B_72,A_73] :
      ( ~ r2_hidden('#skF_2'(A_70,B_71),B_72)
      | ~ r2_hidden(A_73,B_72)
      | ~ r1_tarski(B_71,k1_xboole_0)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_147,c_10])).

tff(c_166,plain,(
    ! [A_73,A_6,B_64,A_63] :
      ( ~ r2_hidden(A_73,A_6)
      | ~ r1_tarski(B_64,k1_xboole_0)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_146,c_156])).

tff(c_170,plain,(
    ! [B_64,A_63] :
      ( ~ r1_tarski(B_64,k1_xboole_0)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_719,plain,(
    ! [A_175,C_176,B_177] :
      ( ~ r1_tarski(k1_funct_1(A_175,C_176),k1_xboole_0)
      | ~ r2_hidden(C_176,k1_relat_1(B_177))
      | ~ v5_funct_1(B_177,A_175)
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177)
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(resolution,[status(thm)],[c_307,c_170])).

tff(c_721,plain,(
    ! [A_1,A_50,B_177] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_1,k1_relat_1(A_50)),k1_relat_1(B_177))
      | ~ v5_funct_1(B_177,A_50)
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50)
      | r1_tarski(A_1,k1_relat_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_719])).

tff(c_773,plain,(
    ! [A_190,A_191,B_192] :
      ( ~ r2_hidden('#skF_1'(A_190,k1_relat_1(A_191)),k1_relat_1(B_192))
      | ~ v5_funct_1(B_192,A_191)
      | ~ v1_funct_1(B_192)
      | ~ v1_relat_1(B_192)
      | r1_tarski(A_190,k1_relat_1(A_191))
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_721])).

tff(c_804,plain,(
    ! [B_196,A_197] :
      ( ~ v5_funct_1(B_196,A_197)
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196)
      | ~ v1_funct_1(A_197)
      | ~ v1_relat_1(A_197)
      | r1_tarski(k1_relat_1(B_196),k1_relat_1(A_197)) ) ),
    inference(resolution,[status(thm)],[c_6,c_773])).

tff(c_28,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_829,plain,
    ( ~ v5_funct_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_804,c_28])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_829])).

tff(c_844,plain,(
    ! [A_73,A_6] : ~ r2_hidden(A_73,A_6) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_854,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,B_2) ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_6])).

tff(c_862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.49  
% 3.26/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.50  %$ v5_funct_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.26/1.50  
% 3.26/1.50  %Foreground sorts:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Background operators:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Foreground operators:
% 3.26/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.26/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.50  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 3.26/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.50  
% 3.26/1.51  tff(f_95, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (((v1_relat_1(B) & v1_funct_1(B)) & v5_funct_1(B, A)) => r1_tarski(k1_relat_1(B), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_1)).
% 3.26/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.26/1.51  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.51  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.26/1.51  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 3.26/1.51  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 3.26/1.51  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.51  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.51  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.51  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.51  tff(c_30, plain, (v5_funct_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.51  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.26/1.51  tff(c_90, plain, (![A_50, B_51]: (k1_funct_1(A_50, B_51)=k1_xboole_0 | r2_hidden(B_51, k1_relat_1(A_50)) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.26/1.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.51  tff(c_98, plain, (![A_1, A_50]: (r1_tarski(A_1, k1_relat_1(A_50)) | k1_funct_1(A_50, '#skF_1'(A_1, k1_relat_1(A_50)))=k1_xboole_0 | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_90, c_4])).
% 3.26/1.51  tff(c_307, plain, (![B_95, C_96, A_97]: (r2_hidden(k1_funct_1(B_95, C_96), k1_funct_1(A_97, C_96)) | ~r2_hidden(C_96, k1_relat_1(B_95)) | ~v5_funct_1(B_95, A_97) | ~v1_funct_1(B_95) | ~v1_relat_1(B_95) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.26/1.51  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.26/1.51  tff(c_49, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.51  tff(c_67, plain, (![A_44, B_45, B_46]: (r2_hidden('#skF_2'(A_44, B_45), B_46) | ~r1_tarski(B_45, B_46) | ~r2_hidden(A_44, B_45))), inference(resolution, [status(thm)], [c_12, c_49])).
% 3.26/1.51  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.51  tff(c_140, plain, (![A_63, B_64, B_65, B_66]: (r2_hidden('#skF_2'(A_63, B_64), B_65) | ~r1_tarski(B_66, B_65) | ~r1_tarski(B_64, B_66) | ~r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_67, c_2])).
% 3.26/1.51  tff(c_146, plain, (![A_63, B_64, A_6]: (r2_hidden('#skF_2'(A_63, B_64), A_6) | ~r1_tarski(B_64, k1_xboole_0) | ~r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_8, c_140])).
% 3.26/1.51  tff(c_147, plain, (![A_67, B_68, A_69]: (r2_hidden('#skF_2'(A_67, B_68), A_69) | ~r1_tarski(B_68, k1_xboole_0) | ~r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_8, c_140])).
% 3.26/1.51  tff(c_10, plain, (![D_13, A_7, B_8]: (~r2_hidden(D_13, '#skF_2'(A_7, B_8)) | ~r2_hidden(D_13, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.26/1.51  tff(c_156, plain, (![A_70, B_71, B_72, A_73]: (~r2_hidden('#skF_2'(A_70, B_71), B_72) | ~r2_hidden(A_73, B_72) | ~r1_tarski(B_71, k1_xboole_0) | ~r2_hidden(A_70, B_71))), inference(resolution, [status(thm)], [c_147, c_10])).
% 3.26/1.51  tff(c_166, plain, (![A_73, A_6, B_64, A_63]: (~r2_hidden(A_73, A_6) | ~r1_tarski(B_64, k1_xboole_0) | ~r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_146, c_156])).
% 3.26/1.51  tff(c_170, plain, (![B_64, A_63]: (~r1_tarski(B_64, k1_xboole_0) | ~r2_hidden(A_63, B_64))), inference(splitLeft, [status(thm)], [c_166])).
% 3.26/1.51  tff(c_719, plain, (![A_175, C_176, B_177]: (~r1_tarski(k1_funct_1(A_175, C_176), k1_xboole_0) | ~r2_hidden(C_176, k1_relat_1(B_177)) | ~v5_funct_1(B_177, A_175) | ~v1_funct_1(B_177) | ~v1_relat_1(B_177) | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(resolution, [status(thm)], [c_307, c_170])).
% 3.26/1.51  tff(c_721, plain, (![A_1, A_50, B_177]: (~r1_tarski(k1_xboole_0, k1_xboole_0) | ~r2_hidden('#skF_1'(A_1, k1_relat_1(A_50)), k1_relat_1(B_177)) | ~v5_funct_1(B_177, A_50) | ~v1_funct_1(B_177) | ~v1_relat_1(B_177) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50) | r1_tarski(A_1, k1_relat_1(A_50)) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_98, c_719])).
% 3.26/1.51  tff(c_773, plain, (![A_190, A_191, B_192]: (~r2_hidden('#skF_1'(A_190, k1_relat_1(A_191)), k1_relat_1(B_192)) | ~v5_funct_1(B_192, A_191) | ~v1_funct_1(B_192) | ~v1_relat_1(B_192) | r1_tarski(A_190, k1_relat_1(A_191)) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_721])).
% 3.26/1.51  tff(c_804, plain, (![B_196, A_197]: (~v5_funct_1(B_196, A_197) | ~v1_funct_1(B_196) | ~v1_relat_1(B_196) | ~v1_funct_1(A_197) | ~v1_relat_1(A_197) | r1_tarski(k1_relat_1(B_196), k1_relat_1(A_197)))), inference(resolution, [status(thm)], [c_6, c_773])).
% 3.26/1.51  tff(c_28, plain, (~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.26/1.51  tff(c_829, plain, (~v5_funct_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_804, c_28])).
% 3.26/1.51  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_829])).
% 3.26/1.51  tff(c_844, plain, (![A_73, A_6]: (~r2_hidden(A_73, A_6))), inference(splitRight, [status(thm)], [c_166])).
% 3.26/1.51  tff(c_854, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2))), inference(negUnitSimplification, [status(thm)], [c_844, c_6])).
% 3.26/1.51  tff(c_862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_854, c_28])).
% 3.26/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.51  
% 3.26/1.51  Inference rules
% 3.26/1.51  ----------------------
% 3.26/1.51  #Ref     : 0
% 3.26/1.51  #Sup     : 181
% 3.26/1.51  #Fact    : 0
% 3.26/1.51  #Define  : 0
% 3.26/1.51  #Split   : 3
% 3.26/1.51  #Chain   : 0
% 3.26/1.51  #Close   : 0
% 3.26/1.51  
% 3.26/1.51  Ordering : KBO
% 3.26/1.51  
% 3.26/1.51  Simplification rules
% 3.26/1.51  ----------------------
% 3.26/1.51  #Subsume      : 94
% 3.26/1.51  #Demod        : 23
% 3.26/1.51  #Tautology    : 14
% 3.26/1.51  #SimpNegUnit  : 10
% 3.26/1.51  #BackRed      : 5
% 3.26/1.51  
% 3.26/1.51  #Partial instantiations: 0
% 3.26/1.51  #Strategies tried      : 1
% 3.26/1.51  
% 3.26/1.51  Timing (in seconds)
% 3.26/1.51  ----------------------
% 3.26/1.51  Preprocessing        : 0.31
% 3.26/1.51  Parsing              : 0.16
% 3.26/1.51  CNF conversion       : 0.02
% 3.26/1.51  Main loop            : 0.44
% 3.26/1.51  Inferencing          : 0.16
% 3.26/1.51  Reduction            : 0.10
% 3.26/1.51  Demodulation         : 0.07
% 3.26/1.51  BG Simplification    : 0.02
% 3.26/1.51  Subsumption          : 0.12
% 3.26/1.51  Abstraction          : 0.02
% 3.26/1.52  MUC search           : 0.00
% 3.26/1.52  Cooper               : 0.00
% 3.26/1.52  Total                : 0.78
% 3.26/1.52  Index Insertion      : 0.00
% 3.26/1.52  Index Deletion       : 0.00
% 3.26/1.52  Index Matching       : 0.00
% 3.26/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
