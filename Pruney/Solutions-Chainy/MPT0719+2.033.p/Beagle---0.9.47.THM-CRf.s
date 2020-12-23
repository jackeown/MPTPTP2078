%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   35 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  81 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_83,axiom,(
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

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ r2_hidden(A_77,C_78)
      | ~ r1_xboole_0(k2_tarski(A_77,B_79),C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_77] : ~ r2_hidden(A_77,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_26,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_83,plain,(
    ! [A_80] : ~ r2_hidden(A_80,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_93,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_32,plain,(
    ! [A_54] :
      ( v1_funct_1(A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_92,c_32])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_168,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_5'(A_113,B_114),k1_relat_1(B_114))
      | v5_funct_1(B_114,A_113)
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_174,plain,(
    ! [A_113] :
      ( r2_hidden('#skF_5'(A_113,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_113)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_168])).

tff(c_177,plain,(
    ! [A_113] :
      ( r2_hidden('#skF_5'(A_113,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_110,c_174])).

tff(c_179,plain,(
    ! [A_115] :
      ( v5_funct_1(k1_xboole_0,A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_177])).

tff(c_40,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_182,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_179,c_40])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 19:28:06 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4
% 2.03/1.22  
% 2.03/1.22  %Foreground sorts:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Background operators:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Foreground operators:
% 2.03/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.03/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.22  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.03/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.03/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.03/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.03/1.22  
% 2.03/1.23  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.03/1.23  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.03/1.23  tff(f_50, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.03/1.23  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.03/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.03/1.23  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.03/1.23  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.03/1.23  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.03/1.23  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.23  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.23  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.23  tff(c_77, plain, (![A_77, C_78, B_79]: (~r2_hidden(A_77, C_78) | ~r1_xboole_0(k2_tarski(A_77, B_79), C_78))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.03/1.23  tff(c_82, plain, (![A_77]: (~r2_hidden(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_77])).
% 2.03/1.23  tff(c_26, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.23  tff(c_83, plain, (![A_80]: (~r2_hidden(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_77])).
% 2.03/1.23  tff(c_93, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_83])).
% 2.03/1.23  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.23  tff(c_92, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.03/1.23  tff(c_32, plain, (![A_54]: (v1_funct_1(A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.23  tff(c_110, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_32])).
% 2.03/1.23  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.23  tff(c_168, plain, (![A_113, B_114]: (r2_hidden('#skF_5'(A_113, B_114), k1_relat_1(B_114)) | v5_funct_1(B_114, A_113) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.03/1.23  tff(c_174, plain, (![A_113]: (r2_hidden('#skF_5'(A_113, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_113) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_30, c_168])).
% 2.03/1.23  tff(c_177, plain, (![A_113]: (r2_hidden('#skF_5'(A_113, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_110, c_174])).
% 2.03/1.23  tff(c_179, plain, (![A_115]: (v5_funct_1(k1_xboole_0, A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(negUnitSimplification, [status(thm)], [c_82, c_177])).
% 2.03/1.23  tff(c_40, plain, (~v5_funct_1(k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.03/1.23  tff(c_182, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_179, c_40])).
% 2.03/1.23  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_182])).
% 2.03/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  Inference rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Ref     : 1
% 2.03/1.23  #Sup     : 30
% 2.03/1.23  #Fact    : 0
% 2.03/1.23  #Define  : 0
% 2.03/1.23  #Split   : 0
% 2.03/1.23  #Chain   : 0
% 2.03/1.23  #Close   : 0
% 2.03/1.23  
% 2.03/1.23  Ordering : KBO
% 2.03/1.23  
% 2.03/1.23  Simplification rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Subsume      : 0
% 2.03/1.23  #Demod        : 5
% 2.03/1.23  #Tautology    : 21
% 2.03/1.23  #SimpNegUnit  : 1
% 2.03/1.23  #BackRed      : 0
% 2.03/1.23  
% 2.03/1.23  #Partial instantiations: 0
% 2.03/1.23  #Strategies tried      : 1
% 2.03/1.23  
% 2.03/1.23  Timing (in seconds)
% 2.03/1.23  ----------------------
% 2.14/1.23  Preprocessing        : 0.32
% 2.14/1.23  Parsing              : 0.17
% 2.14/1.23  CNF conversion       : 0.02
% 2.14/1.23  Main loop            : 0.15
% 2.14/1.23  Inferencing          : 0.07
% 2.14/1.23  Reduction            : 0.04
% 2.14/1.23  Demodulation         : 0.03
% 2.14/1.23  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.02
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.50
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
