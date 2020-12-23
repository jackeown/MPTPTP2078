%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   53 (  64 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 (  89 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_78,axiom,(
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

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_45,plain,(
    ! [A_30] :
      ( v1_relat_1(A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_40,plain,(
    ! [A_29] :
      ( v1_funct_1(A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_173,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50,B_51),k1_relat_1(B_51))
      | v5_funct_1(B_51,A_50)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_38,C_39,B_40] :
      ( ~ r2_hidden(A_38,C_39)
      | ~ r1_xboole_0(k2_tarski(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,(
    ! [A_38] : ~ r2_hidden(A_38,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_50,plain,(
    ! [A_31] :
      ( v1_xboole_0(k2_relat_1(A_31))
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_63,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) = k1_xboole_0
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_71,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_152,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),k2_relat_1(B_46))
      | ~ r2_hidden(A_45,k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_158,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_45,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_152])).

tff(c_161,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_45,k1_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_158])).

tff(c_162,plain,(
    ! [A_45] : ~ r2_hidden(A_45,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_161])).

tff(c_181,plain,(
    ! [A_50] :
      ( v5_funct_1(k1_xboole_0,A_50)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_173,c_162])).

tff(c_186,plain,(
    ! [A_52] :
      ( v5_funct_1(k1_xboole_0,A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_44,c_181])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_189,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_28])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:23:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.31  
% 1.94/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.31  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.94/1.31  
% 1.94/1.31  %Foreground sorts:
% 1.94/1.31  
% 1.94/1.31  
% 1.94/1.31  %Background operators:
% 1.94/1.31  
% 1.94/1.31  
% 1.94/1.31  %Foreground operators:
% 1.94/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.31  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.94/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.94/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.94/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.31  
% 1.94/1.32  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.94/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.32  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.94/1.32  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.94/1.32  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.94/1.32  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.94/1.32  tff(f_41, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.94/1.32  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.94/1.32  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.32  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 1.94/1.32  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.94/1.32  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.94/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.32  tff(c_45, plain, (![A_30]: (v1_relat_1(A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.32  tff(c_49, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.94/1.32  tff(c_40, plain, (![A_29]: (v1_funct_1(A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.32  tff(c_44, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_40])).
% 1.94/1.32  tff(c_173, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50, B_51), k1_relat_1(B_51)) | v5_funct_1(B_51, A_50) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.94/1.32  tff(c_6, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.32  tff(c_136, plain, (![A_38, C_39, B_40]: (~r2_hidden(A_38, C_39) | ~r1_xboole_0(k2_tarski(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.32  tff(c_141, plain, (![A_38]: (~r2_hidden(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_136])).
% 1.94/1.32  tff(c_50, plain, (![A_31]: (v1_xboole_0(k2_relat_1(A_31)) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.32  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.94/1.32  tff(c_63, plain, (![A_32]: (k2_relat_1(A_32)=k1_xboole_0 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_50, c_4])).
% 1.94/1.32  tff(c_71, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_63])).
% 1.94/1.32  tff(c_152, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), k2_relat_1(B_46)) | ~r2_hidden(A_45, k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.32  tff(c_158, plain, (![A_45]: (r2_hidden('#skF_1'(A_45, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_45, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_152])).
% 1.94/1.32  tff(c_161, plain, (![A_45]: (r2_hidden('#skF_1'(A_45, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_45, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_158])).
% 1.94/1.32  tff(c_162, plain, (![A_45]: (~r2_hidden(A_45, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_141, c_161])).
% 1.94/1.32  tff(c_181, plain, (![A_50]: (v5_funct_1(k1_xboole_0, A_50) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_173, c_162])).
% 1.94/1.32  tff(c_186, plain, (![A_52]: (v5_funct_1(k1_xboole_0, A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_44, c_181])).
% 1.94/1.32  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.94/1.32  tff(c_189, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_186, c_28])).
% 1.94/1.32  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_189])).
% 1.94/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.32  
% 1.94/1.32  Inference rules
% 1.94/1.32  ----------------------
% 1.94/1.32  #Ref     : 0
% 1.94/1.32  #Sup     : 33
% 1.94/1.32  #Fact    : 0
% 1.94/1.32  #Define  : 0
% 1.94/1.32  #Split   : 0
% 1.94/1.32  #Chain   : 0
% 1.94/1.32  #Close   : 0
% 1.94/1.32  
% 1.94/1.32  Ordering : KBO
% 1.94/1.32  
% 1.94/1.32  Simplification rules
% 1.94/1.32  ----------------------
% 1.94/1.32  #Subsume      : 2
% 1.94/1.32  #Demod        : 21
% 1.94/1.32  #Tautology    : 18
% 1.94/1.32  #SimpNegUnit  : 2
% 1.94/1.32  #BackRed      : 0
% 1.94/1.32  
% 1.94/1.32  #Partial instantiations: 0
% 1.94/1.32  #Strategies tried      : 1
% 1.94/1.32  
% 1.94/1.32  Timing (in seconds)
% 1.94/1.32  ----------------------
% 1.94/1.33  Preprocessing        : 0.35
% 1.94/1.33  Parsing              : 0.19
% 1.94/1.33  CNF conversion       : 0.02
% 1.94/1.33  Main loop            : 0.16
% 1.94/1.33  Inferencing          : 0.06
% 1.94/1.33  Reduction            : 0.05
% 1.94/1.33  Demodulation         : 0.03
% 1.94/1.33  BG Simplification    : 0.02
% 1.94/1.33  Subsumption          : 0.03
% 1.94/1.33  Abstraction          : 0.01
% 1.94/1.33  MUC search           : 0.00
% 1.94/1.33  Cooper               : 0.00
% 1.94/1.33  Total                : 0.54
% 1.94/1.33  Index Insertion      : 0.00
% 1.94/1.33  Index Deletion       : 0.00
% 1.94/1.33  Index Matching       : 0.00
% 1.94/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
