%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:00 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   44 (  84 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 256 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_73,plain,(
    ! [A_29] :
      ( k1_relat_1(k2_funct_1(A_29)) = k2_relat_1(A_29)
      | ~ v1_funct_1(k2_funct_1(A_29))
      | ~ v1_relat_1(k2_funct_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    ! [A_30] :
      ( k1_relat_1(k2_funct_1(A_30)) = k2_relat_1(A_30)
      | ~ v1_funct_1(k2_funct_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_82,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_78])).

tff(c_36,plain,(
    ! [A_22] :
      ( k5_relat_1(k2_funct_1(A_22),A_22) = k6_relat_1(k2_relat_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_67,plain,(
    ! [A_27,B_28] :
      ( v2_funct_1(A_27)
      | k6_relat_1(k1_relat_1(A_27)) != k5_relat_1(A_27,B_28)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,(
    ! [A_40] :
      ( v2_funct_1(k2_funct_1(A_40))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_40))) != k6_relat_1(k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40)
      | ~ v1_funct_1(k2_funct_1(A_40))
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_67])).

tff(c_157,plain,(
    ! [A_41] :
      ( v2_funct_1(k2_funct_1(A_41))
      | ~ v1_funct_1(k2_funct_1(A_41))
      | ~ v1_relat_1(k2_funct_1(A_41))
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_152])).

tff(c_40,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_160,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_157,c_40])).

tff(c_163,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_160])).

tff(c_164,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_167,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_167])).

tff(c_172,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_176,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_172])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.09/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.09/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.09/1.30  
% 2.09/1.31  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 2.09/1.31  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.09/1.31  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 2.09/1.31  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.09/1.31  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 2.09/1.31  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.09/1.31  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.09/1.31  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.31  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.31  tff(c_42, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.09/1.31  tff(c_73, plain, (![A_29]: (k1_relat_1(k2_funct_1(A_29))=k2_relat_1(A_29) | ~v1_funct_1(k2_funct_1(A_29)) | ~v1_relat_1(k2_funct_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.31  tff(c_78, plain, (![A_30]: (k1_relat_1(k2_funct_1(A_30))=k2_relat_1(A_30) | ~v1_funct_1(k2_funct_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_4, c_73])).
% 2.09/1.31  tff(c_82, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_78])).
% 2.09/1.31  tff(c_36, plain, (![A_22]: (k5_relat_1(k2_funct_1(A_22), A_22)=k6_relat_1(k2_relat_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.09/1.31  tff(c_67, plain, (![A_27, B_28]: (v2_funct_1(A_27) | k6_relat_1(k1_relat_1(A_27))!=k5_relat_1(A_27, B_28) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.31  tff(c_152, plain, (![A_40]: (v2_funct_1(k2_funct_1(A_40)) | k6_relat_1(k1_relat_1(k2_funct_1(A_40)))!=k6_relat_1(k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40) | ~v1_funct_1(k2_funct_1(A_40)) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_36, c_67])).
% 2.09/1.31  tff(c_157, plain, (![A_41]: (v2_funct_1(k2_funct_1(A_41)) | ~v1_funct_1(k2_funct_1(A_41)) | ~v1_relat_1(k2_funct_1(A_41)) | ~v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_82, c_152])).
% 2.09/1.31  tff(c_40, plain, (~v2_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.09/1.31  tff(c_160, plain, (~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_157, c_40])).
% 2.09/1.31  tff(c_163, plain, (~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_160])).
% 2.09/1.31  tff(c_164, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_163])).
% 2.09/1.31  tff(c_167, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4, c_164])).
% 2.09/1.31  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_167])).
% 2.09/1.31  tff(c_172, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_163])).
% 2.09/1.31  tff(c_176, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2, c_172])).
% 2.09/1.31  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_176])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 0
% 2.09/1.31  #Sup     : 30
% 2.09/1.31  #Fact    : 0
% 2.09/1.31  #Define  : 0
% 2.09/1.31  #Split   : 1
% 2.09/1.31  #Chain   : 0
% 2.09/1.31  #Close   : 0
% 2.09/1.31  
% 2.09/1.31  Ordering : KBO
% 2.09/1.31  
% 2.09/1.31  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 3
% 2.09/1.31  #Demod        : 7
% 2.09/1.31  #Tautology    : 15
% 2.09/1.31  #SimpNegUnit  : 0
% 2.09/1.31  #BackRed      : 0
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.32  ----------------------
% 2.09/1.32  Preprocessing        : 0.35
% 2.09/1.32  Parsing              : 0.18
% 2.09/1.32  CNF conversion       : 0.03
% 2.09/1.32  Main loop            : 0.18
% 2.09/1.32  Inferencing          : 0.06
% 2.09/1.32  Reduction            : 0.05
% 2.09/1.32  Demodulation         : 0.04
% 2.09/1.32  BG Simplification    : 0.02
% 2.09/1.32  Subsumption          : 0.04
% 2.09/1.32  Abstraction          : 0.01
% 2.09/1.32  MUC search           : 0.00
% 2.09/1.32  Cooper               : 0.00
% 2.09/1.32  Total                : 0.56
% 2.09/1.32  Index Insertion      : 0.00
% 2.09/1.32  Index Deletion       : 0.00
% 2.09/1.32  Index Matching       : 0.00
% 2.09/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
