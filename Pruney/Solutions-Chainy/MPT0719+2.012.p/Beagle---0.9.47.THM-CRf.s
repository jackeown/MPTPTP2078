%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
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
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

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
    ! [A_27] :
      ( v1_relat_1(A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_40,plain,(
    ! [A_26] :
      ( v1_funct_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_173,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),k1_relat_1(B_45))
      | v5_funct_1(B_45,A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden(A_33,B_34)
      | ~ r1_xboole_0(k1_tarski(A_33),B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_33] : ~ r2_hidden(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_59,plain,(
    ! [A_29] :
      ( v1_xboole_0(k2_relat_1(A_29))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_74,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) = k1_xboole_0
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_59,c_4])).

tff(c_82,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_152,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),k2_relat_1(B_40))
      | ~ r2_hidden(A_39,k1_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_158,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_1'(A_39,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_39,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_152])).

tff(c_161,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_1'(A_39,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_39,k1_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_158])).

tff(c_162,plain,(
    ! [A_39] : ~ r2_hidden(A_39,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_161])).

tff(c_181,plain,(
    ! [A_44] :
      ( v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_173,c_162])).

tff(c_186,plain,(
    ! [A_46] :
      ( v5_funct_1(k1_xboole_0,A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:29:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.19  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.98/1.19  
% 1.98/1.19  %Foreground sorts:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Background operators:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Foreground operators:
% 1.98/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.19  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.98/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.19  
% 1.98/1.21  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.98/1.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.21  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.98/1.21  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.98/1.21  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.98/1.21  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.98/1.21  tff(f_41, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.98/1.21  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.98/1.21  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.98/1.21  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 1.98/1.21  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.98/1.21  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.98/1.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.98/1.21  tff(c_45, plain, (![A_27]: (v1_relat_1(A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.21  tff(c_49, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.98/1.21  tff(c_40, plain, (![A_26]: (v1_funct_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.21  tff(c_44, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_40])).
% 1.98/1.21  tff(c_173, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), k1_relat_1(B_45)) | v5_funct_1(B_45, A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.98/1.21  tff(c_6, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.21  tff(c_83, plain, (![A_33, B_34]: (~r2_hidden(A_33, B_34) | ~r1_xboole_0(k1_tarski(A_33), B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.21  tff(c_88, plain, (![A_33]: (~r2_hidden(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_83])).
% 1.98/1.21  tff(c_59, plain, (![A_29]: (v1_xboole_0(k2_relat_1(A_29)) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.21  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.98/1.21  tff(c_74, plain, (![A_32]: (k2_relat_1(A_32)=k1_xboole_0 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_59, c_4])).
% 1.98/1.21  tff(c_82, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_74])).
% 1.98/1.21  tff(c_152, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), k2_relat_1(B_40)) | ~r2_hidden(A_39, k1_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.21  tff(c_158, plain, (![A_39]: (r2_hidden('#skF_1'(A_39, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_39, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_152])).
% 1.98/1.21  tff(c_161, plain, (![A_39]: (r2_hidden('#skF_1'(A_39, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_39, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_158])).
% 1.98/1.21  tff(c_162, plain, (![A_39]: (~r2_hidden(A_39, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_88, c_161])).
% 1.98/1.21  tff(c_181, plain, (![A_44]: (v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_173, c_162])).
% 1.98/1.21  tff(c_186, plain, (![A_46]: (v5_funct_1(k1_xboole_0, A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_44, c_181])).
% 1.98/1.21  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.98/1.21  tff(c_189, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_186, c_28])).
% 1.98/1.21  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_189])).
% 1.98/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  Inference rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Ref     : 0
% 1.98/1.21  #Sup     : 33
% 1.98/1.21  #Fact    : 0
% 1.98/1.21  #Define  : 0
% 1.98/1.21  #Split   : 0
% 1.98/1.21  #Chain   : 0
% 1.98/1.21  #Close   : 0
% 1.98/1.21  
% 1.98/1.21  Ordering : KBO
% 1.98/1.21  
% 1.98/1.21  Simplification rules
% 1.98/1.21  ----------------------
% 1.98/1.21  #Subsume      : 2
% 1.98/1.21  #Demod        : 21
% 1.98/1.21  #Tautology    : 18
% 1.98/1.21  #SimpNegUnit  : 2
% 1.98/1.21  #BackRed      : 0
% 1.98/1.21  
% 1.98/1.21  #Partial instantiations: 0
% 1.98/1.21  #Strategies tried      : 1
% 1.98/1.21  
% 1.98/1.21  Timing (in seconds)
% 1.98/1.21  ----------------------
% 1.98/1.21  Preprocessing        : 0.31
% 1.98/1.21  Parsing              : 0.16
% 1.98/1.21  CNF conversion       : 0.02
% 1.98/1.21  Main loop            : 0.14
% 1.98/1.21  Inferencing          : 0.06
% 1.98/1.21  Reduction            : 0.04
% 1.98/1.21  Demodulation         : 0.03
% 1.98/1.21  BG Simplification    : 0.01
% 1.98/1.21  Subsumption          : 0.02
% 1.98/1.21  Abstraction          : 0.01
% 1.98/1.21  MUC search           : 0.00
% 1.98/1.21  Cooper               : 0.00
% 1.98/1.21  Total                : 0.48
% 1.98/1.21  Index Insertion      : 0.00
% 1.98/1.21  Index Deletion       : 0.00
% 1.98/1.21  Index Matching       : 0.00
% 1.98/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
