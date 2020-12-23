%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 103 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 180 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(k1_tarski(A_5),B_6)
      | r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_108,plain,(
    ! [A_37,B_38] :
      ( k7_relat_1(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(B_38,k1_relat_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_127,plain,(
    ! [A_41,A_42] :
      ( k7_relat_1(A_41,k1_tarski(A_42)) = k1_xboole_0
      | ~ v1_relat_1(A_41)
      | r2_hidden(A_42,k1_relat_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( k1_tarski(k1_funct_1(B_19,A_18)) = k11_relat_1(B_19,A_18)
      | ~ r2_hidden(A_18,k1_relat_1(B_19))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_135,plain,(
    ! [A_43,A_44] :
      ( k1_tarski(k1_funct_1(A_43,A_44)) = k11_relat_1(A_43,A_44)
      | ~ v1_funct_1(A_43)
      | k7_relat_1(A_43,k1_tarski(A_44)) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_127,c_30])).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_144,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_32])).

tff(c_151,plain,(
    k1_tarski(k1_funct_1('#skF_2','#skF_1')) = k11_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2,c_26,c_144])).

tff(c_20,plain,(
    ! [A_10,B_12] :
      ( k9_relat_1(A_10,k1_tarski(B_12)) = k11_relat_1(A_10,B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    ! [B_33,A_34] :
      ( k2_relat_1(k7_relat_1(B_33,A_34)) = k9_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_91,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_32])).

tff(c_97,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_91])).

tff(c_119,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_97])).

tff(c_121,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_119])).

tff(c_153,plain,(
    ~ r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_121])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [C_22,B_23] : r1_tarski(k1_tarski(C_22),k2_tarski(B_23,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_59,plain,(
    ! [A_2] : r1_tarski(k1_tarski(A_2),k1_tarski(A_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_174,plain,(
    r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k11_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_59])).

tff(c_181,plain,(
    r1_tarski(k11_relat_1('#skF_2','#skF_1'),k11_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_174])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.89/1.22  
% 1.89/1.22  %Foreground sorts:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Background operators:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Foreground operators:
% 1.89/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.22  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.89/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.89/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.22  
% 2.12/1.23  tff(f_85, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.12/1.23  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.23  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.23  tff(f_36, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.12/1.23  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.12/1.23  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 2.12/1.23  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.12/1.23  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.12/1.23  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.23  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.12/1.23  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.12/1.23  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.12/1.23  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.23  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.23  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(k1_tarski(A_5), B_6) | r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.23  tff(c_108, plain, (![A_37, B_38]: (k7_relat_1(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(B_38, k1_relat_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.23  tff(c_127, plain, (![A_41, A_42]: (k7_relat_1(A_41, k1_tarski(A_42))=k1_xboole_0 | ~v1_relat_1(A_41) | r2_hidden(A_42, k1_relat_1(A_41)))), inference(resolution, [status(thm)], [c_8, c_108])).
% 2.12/1.23  tff(c_30, plain, (![B_19, A_18]: (k1_tarski(k1_funct_1(B_19, A_18))=k11_relat_1(B_19, A_18) | ~r2_hidden(A_18, k1_relat_1(B_19)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.23  tff(c_135, plain, (![A_43, A_44]: (k1_tarski(k1_funct_1(A_43, A_44))=k11_relat_1(A_43, A_44) | ~v1_funct_1(A_43) | k7_relat_1(A_43, k1_tarski(A_44))=k1_xboole_0 | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_127, c_30])).
% 2.12/1.23  tff(c_32, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.12/1.23  tff(c_144, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135, c_32])).
% 2.12/1.23  tff(c_151, plain, (k1_tarski(k1_funct_1('#skF_2', '#skF_1'))=k11_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2, c_26, c_144])).
% 2.12/1.23  tff(c_20, plain, (![A_10, B_12]: (k9_relat_1(A_10, k1_tarski(B_12))=k11_relat_1(A_10, B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.23  tff(c_85, plain, (![B_33, A_34]: (k2_relat_1(k7_relat_1(B_33, A_34))=k9_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.12/1.23  tff(c_91, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_32])).
% 2.12/1.23  tff(c_97, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_91])).
% 2.12/1.23  tff(c_119, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_97])).
% 2.12/1.23  tff(c_121, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_119])).
% 2.12/1.23  tff(c_153, plain, (~r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_121])).
% 2.12/1.23  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.23  tff(c_56, plain, (![C_22, B_23]: (r1_tarski(k1_tarski(C_22), k2_tarski(B_23, C_22)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.23  tff(c_59, plain, (![A_2]: (r1_tarski(k1_tarski(A_2), k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_56])).
% 2.12/1.23  tff(c_174, plain, (r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k11_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_59])).
% 2.12/1.23  tff(c_181, plain, (r1_tarski(k11_relat_1('#skF_2', '#skF_1'), k11_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_174])).
% 2.12/1.23  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_181])).
% 2.12/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.23  
% 2.12/1.23  Inference rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Ref     : 0
% 2.12/1.23  #Sup     : 41
% 2.12/1.23  #Fact    : 0
% 2.12/1.23  #Define  : 0
% 2.12/1.23  #Split   : 1
% 2.12/1.23  #Chain   : 0
% 2.12/1.23  #Close   : 0
% 2.12/1.23  
% 2.12/1.23  Ordering : KBO
% 2.12/1.23  
% 2.12/1.23  Simplification rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Subsume      : 2
% 2.12/1.23  #Demod        : 19
% 2.12/1.23  #Tautology    : 24
% 2.12/1.23  #SimpNegUnit  : 1
% 2.12/1.23  #BackRed      : 3
% 2.12/1.23  
% 2.12/1.23  #Partial instantiations: 0
% 2.12/1.23  #Strategies tried      : 1
% 2.12/1.23  
% 2.12/1.23  Timing (in seconds)
% 2.12/1.23  ----------------------
% 2.12/1.24  Preprocessing        : 0.30
% 2.12/1.24  Parsing              : 0.15
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.17
% 2.12/1.24  Inferencing          : 0.06
% 2.12/1.24  Reduction            : 0.06
% 2.12/1.24  Demodulation         : 0.04
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.02
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.49
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
