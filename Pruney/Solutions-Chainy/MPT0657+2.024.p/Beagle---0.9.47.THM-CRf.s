%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:07 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 191 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(B) = k1_relat_1(A)
                & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( k2_relat_1(B) = A
                  & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                  & k5_relat_1(C,D) = k6_relat_1(A) )
               => D = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

tff(c_18,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_80,plain,(
    ! [D_20,B_21,C_22] :
      ( D_20 = B_21
      | k6_relat_1(k2_relat_1(B_21)) != k5_relat_1(C_22,D_20)
      | k6_relat_1(k1_relat_1(D_20)) != k5_relat_1(B_21,C_22)
      | ~ v1_funct_1(D_20)
      | ~ v1_relat_1(D_20)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_165,plain,(
    ! [A_37,B_38] :
      ( k2_funct_1(A_37) = B_38
      | k6_relat_1(k2_relat_1(B_38)) != k6_relat_1(k1_relat_1(A_37))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_37))) != k5_relat_1(B_38,A_37)
      | ~ v1_funct_1(k2_funct_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_80])).

tff(c_173,plain,(
    ! [A_37] :
      ( k2_funct_1(A_37) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_37)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_37))) != k5_relat_1('#skF_2',A_37)
      | ~ v1_funct_1(k2_funct_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_165])).

tff(c_182,plain,(
    ! [A_40] :
      ( k2_funct_1(A_40) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_40)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k1_relat_1(k2_funct_1(A_40))) != k5_relat_1('#skF_2',A_40)
      | ~ v1_funct_1(k2_funct_1(A_40))
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_173])).

tff(c_219,plain,(
    ! [A_47] :
      ( k2_funct_1(A_47) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_47)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_47)) != k5_relat_1('#skF_2',A_47)
      | ~ v1_funct_1(k2_funct_1(A_47))
      | ~ v1_relat_1(k2_funct_1(A_47))
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47)
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_182])).

tff(c_224,plain,(
    ! [A_48] :
      ( k2_funct_1(A_48) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_48)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_48)) != k5_relat_1('#skF_2',A_48)
      | ~ v1_funct_1(k2_funct_1(A_48))
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_229,plain,(
    ! [A_49] :
      ( k2_funct_1(A_49) = '#skF_2'
      | k6_relat_1(k1_relat_1(A_49)) != k6_relat_1(k1_relat_1('#skF_1'))
      | k6_relat_1(k2_relat_1(A_49)) != k5_relat_1('#skF_2',A_49)
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_224])).

tff(c_235,plain,
    ( k2_funct_1('#skF_1') = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_229])).

tff(c_241,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_235])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:20:52 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.69/1.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.69/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.41  
% 2.69/1.42  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 2.69/1.42  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 2.69/1.42  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.69/1.42  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.69/1.42  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l72_funct_1)).
% 2.69/1.42  tff(c_18, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_20, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_4, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.42  tff(c_6, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.42  tff(c_12, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.42  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_22, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_16, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.69/1.42  tff(c_80, plain, (![D_20, B_21, C_22]: (D_20=B_21 | k6_relat_1(k2_relat_1(B_21))!=k5_relat_1(C_22, D_20) | k6_relat_1(k1_relat_1(D_20))!=k5_relat_1(B_21, C_22) | ~v1_funct_1(D_20) | ~v1_relat_1(D_20) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.42  tff(c_165, plain, (![A_37, B_38]: (k2_funct_1(A_37)=B_38 | k6_relat_1(k2_relat_1(B_38))!=k6_relat_1(k1_relat_1(A_37)) | k6_relat_1(k1_relat_1(k2_funct_1(A_37)))!=k5_relat_1(B_38, A_37) | ~v1_funct_1(k2_funct_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_16, c_80])).
% 2.69/1.42  tff(c_173, plain, (![A_37]: (k2_funct_1(A_37)='#skF_2' | k6_relat_1(k1_relat_1(A_37))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_37)))!=k5_relat_1('#skF_2', A_37) | ~v1_funct_1(k2_funct_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_22, c_165])).
% 2.69/1.42  tff(c_182, plain, (![A_40]: (k2_funct_1(A_40)='#skF_2' | k6_relat_1(k1_relat_1(A_40))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k1_relat_1(k2_funct_1(A_40)))!=k5_relat_1('#skF_2', A_40) | ~v1_funct_1(k2_funct_1(A_40)) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_173])).
% 2.69/1.42  tff(c_219, plain, (![A_47]: (k2_funct_1(A_47)='#skF_2' | k6_relat_1(k1_relat_1(A_47))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k2_relat_1(A_47))!=k5_relat_1('#skF_2', A_47) | ~v1_funct_1(k2_funct_1(A_47)) | ~v1_relat_1(k2_funct_1(A_47)) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_182])).
% 2.69/1.42  tff(c_224, plain, (![A_48]: (k2_funct_1(A_48)='#skF_2' | k6_relat_1(k1_relat_1(A_48))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k2_relat_1(A_48))!=k5_relat_1('#skF_2', A_48) | ~v1_funct_1(k2_funct_1(A_48)) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_6, c_219])).
% 2.69/1.42  tff(c_229, plain, (![A_49]: (k2_funct_1(A_49)='#skF_2' | k6_relat_1(k1_relat_1(A_49))!=k6_relat_1(k1_relat_1('#skF_1')) | k6_relat_1(k2_relat_1(A_49))!=k5_relat_1('#skF_2', A_49) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_4, c_224])).
% 2.69/1.42  tff(c_235, plain, (k2_funct_1('#skF_1')='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_229])).
% 2.69/1.42  tff(c_241, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_235])).
% 2.69/1.42  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_241])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 1
% 2.69/1.42  #Sup     : 50
% 2.69/1.42  #Fact    : 0
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 2
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 10
% 2.69/1.42  #Demod        : 27
% 2.69/1.42  #Tautology    : 16
% 2.69/1.42  #SimpNegUnit  : 1
% 2.69/1.42  #BackRed      : 0
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.33
% 2.69/1.42  Parsing              : 0.18
% 2.69/1.42  CNF conversion       : 0.02
% 2.69/1.42  Main loop            : 0.27
% 2.69/1.42  Inferencing          : 0.10
% 2.69/1.42  Reduction            : 0.07
% 2.69/1.42  Demodulation         : 0.05
% 2.69/1.42  BG Simplification    : 0.02
% 2.69/1.42  Subsumption          : 0.08
% 2.69/1.42  Abstraction          : 0.01
% 2.69/1.42  MUC search           : 0.00
% 2.69/1.42  Cooper               : 0.00
% 2.69/1.42  Total                : 0.63
% 2.69/1.42  Index Insertion      : 0.00
% 2.69/1.42  Index Deletion       : 0.00
% 2.69/1.42  Index Matching       : 0.00
% 2.69/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
