%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:49 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 167 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 677 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( v2_wellord1(A)
                    & r3_wellord1(A,B,C) )
                 => v2_wellord1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
               => ( ( v1_relat_2(A)
                   => v1_relat_2(B) )
                  & ( v8_relat_2(A)
                   => v8_relat_2(B) )
                  & ( v6_relat_2(A)
                   => v6_relat_2(B) )
                  & ( v4_relat_2(A)
                   => v4_relat_2(B) )
                  & ( v1_wellord1(A)
                   => v1_wellord1(B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    v2_wellord1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_1] :
      ( v6_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ~ v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_39,plain,(
    ! [A_15] :
      ( v1_relat_2(A_15)
      | ~ v2_wellord1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,
    ( v1_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_45,plain,(
    v1_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_26,plain,(
    r3_wellord1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_76,plain,(
    ! [B_22,A_23,C_24] :
      ( v1_relat_2(B_22)
      | ~ v1_relat_2(A_23)
      | ~ r3_wellord1(A_23,B_22,C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_79,plain,
    ( v1_relat_2('#skF_2')
    | ~ v1_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_82,plain,(
    v1_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_45,c_79])).

tff(c_8,plain,(
    ! [A_1] :
      ( v4_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [B_19,A_20,C_21] :
      ( v4_relat_2(B_19)
      | ~ v4_relat_2(A_20)
      | ~ r3_wellord1(A_20,B_19,C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,
    ( v4_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_65,plain,
    ( v4_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_62])).

tff(c_66,plain,(
    ~ v4_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_69,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_73,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_69])).

tff(c_74,plain,(
    v4_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_47,plain,(
    ! [A_17] :
      ( v1_wellord1(A_17)
      | ~ v2_wellord1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,
    ( v1_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_53,plain,(
    v1_wellord1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_50])).

tff(c_83,plain,(
    ! [B_25,A_26,C_27] :
      ( v1_wellord1(B_25)
      | ~ v1_wellord1(A_26)
      | ~ r3_wellord1(A_26,B_25,C_27)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_86,plain,
    ( v1_wellord1('#skF_2')
    | ~ v1_wellord1('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_89,plain,(
    v1_wellord1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_53,c_86])).

tff(c_10,plain,(
    ! [A_1] :
      ( v8_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [B_28,A_29,C_30] :
      ( v8_relat_2(B_28)
      | ~ v8_relat_2(A_29)
      | ~ r3_wellord1(A_29,B_28,C_30)
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,
    ( v8_relat_2('#skF_2')
    | ~ v8_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_96,plain,
    ( v8_relat_2('#skF_2')
    | ~ v8_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_93])).

tff(c_104,plain,(
    ~ v8_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_107,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_107])).

tff(c_112,plain,(
    v8_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_wellord1(A_1)
      | ~ v1_wellord1(A_1)
      | ~ v6_relat_2(A_1)
      | ~ v4_relat_2(A_1)
      | ~ v8_relat_2(A_1)
      | ~ v1_relat_2(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,
    ( v2_wellord1('#skF_2')
    | ~ v1_wellord1('#skF_2')
    | ~ v6_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_2')
    | ~ v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_119,plain,
    ( v2_wellord1('#skF_2')
    | ~ v6_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82,c_74,c_89,c_116])).

tff(c_120,plain,(
    ~ v6_relat_2('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_119])).

tff(c_97,plain,(
    ! [B_31,A_32,C_33] :
      ( v6_relat_2(B_31)
      | ~ v6_relat_2(A_32)
      | ~ r3_wellord1(A_32,B_31,C_33)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_100,plain,
    ( v6_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_97])).

tff(c_103,plain,
    ( v6_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_100])).

tff(c_133,plain,(
    ~ v6_relat_2('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_103])).

tff(c_136,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.31  
% 1.81/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.31  %$ r3_wellord1 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.81/1.31  
% 1.81/1.31  %Foreground sorts:
% 1.81/1.31  
% 1.81/1.31  
% 1.81/1.31  %Background operators:
% 1.81/1.31  
% 1.81/1.31  
% 1.81/1.31  %Foreground operators:
% 1.81/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.31  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 1.81/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.31  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.81/1.31  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 1.81/1.31  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 1.81/1.31  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 1.81/1.31  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.81/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.31  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 1.81/1.31  
% 1.81/1.33  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((v2_wellord1(A) & r3_wellord1(A, B, C)) => v2_wellord1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_wellord1)).
% 1.81/1.33  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 1.81/1.33  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) => (((((v1_relat_2(A) => v1_relat_2(B)) & (v8_relat_2(A) => v8_relat_2(B))) & (v6_relat_2(A) => v6_relat_2(B))) & (v4_relat_2(A) => v4_relat_2(B))) & (v1_wellord1(A) => v1_wellord1(B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_wellord1)).
% 1.81/1.33  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.81/1.33  tff(c_28, plain, (v2_wellord1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.81/1.33  tff(c_6, plain, (![A_1]: (v6_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.33  tff(c_24, plain, (~v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.81/1.33  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.81/1.33  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.81/1.33  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.81/1.33  tff(c_39, plain, (![A_15]: (v1_relat_2(A_15) | ~v2_wellord1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.33  tff(c_42, plain, (v1_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_39])).
% 1.81/1.33  tff(c_45, plain, (v1_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_42])).
% 1.81/1.33  tff(c_26, plain, (r3_wellord1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.81/1.33  tff(c_76, plain, (![B_22, A_23, C_24]: (v1_relat_2(B_22) | ~v1_relat_2(A_23) | ~r3_wellord1(A_23, B_22, C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24) | ~v1_relat_1(B_22) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.81/1.33  tff(c_79, plain, (v1_relat_2('#skF_2') | ~v1_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_76])).
% 1.81/1.33  tff(c_82, plain, (v1_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_45, c_79])).
% 1.81/1.33  tff(c_8, plain, (![A_1]: (v4_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.33  tff(c_59, plain, (![B_19, A_20, C_21]: (v4_relat_2(B_19) | ~v4_relat_2(A_20) | ~r3_wellord1(A_20, B_19, C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21) | ~v1_relat_1(B_19) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.81/1.33  tff(c_62, plain, (v4_relat_2('#skF_2') | ~v4_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_59])).
% 1.81/1.33  tff(c_65, plain, (v4_relat_2('#skF_2') | ~v4_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_62])).
% 1.81/1.33  tff(c_66, plain, (~v4_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_65])).
% 1.81/1.33  tff(c_69, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_66])).
% 1.81/1.33  tff(c_73, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_69])).
% 1.81/1.33  tff(c_74, plain, (v4_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_65])).
% 1.81/1.33  tff(c_47, plain, (![A_17]: (v1_wellord1(A_17) | ~v2_wellord1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.33  tff(c_50, plain, (v1_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_47])).
% 1.81/1.33  tff(c_53, plain, (v1_wellord1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_50])).
% 1.81/1.33  tff(c_83, plain, (![B_25, A_26, C_27]: (v1_wellord1(B_25) | ~v1_wellord1(A_26) | ~r3_wellord1(A_26, B_25, C_27) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27) | ~v1_relat_1(B_25) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.81/1.33  tff(c_86, plain, (v1_wellord1('#skF_2') | ~v1_wellord1('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_83])).
% 1.81/1.33  tff(c_89, plain, (v1_wellord1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_53, c_86])).
% 1.81/1.33  tff(c_10, plain, (![A_1]: (v8_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.33  tff(c_90, plain, (![B_28, A_29, C_30]: (v8_relat_2(B_28) | ~v8_relat_2(A_29) | ~r3_wellord1(A_29, B_28, C_30) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30) | ~v1_relat_1(B_28) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.81/1.33  tff(c_93, plain, (v8_relat_2('#skF_2') | ~v8_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_90])).
% 1.81/1.33  tff(c_96, plain, (v8_relat_2('#skF_2') | ~v8_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_93])).
% 1.81/1.33  tff(c_104, plain, (~v8_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_96])).
% 1.81/1.33  tff(c_107, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_104])).
% 1.81/1.33  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_107])).
% 1.81/1.33  tff(c_112, plain, (v8_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_96])).
% 1.81/1.33  tff(c_2, plain, (![A_1]: (v2_wellord1(A_1) | ~v1_wellord1(A_1) | ~v6_relat_2(A_1) | ~v4_relat_2(A_1) | ~v8_relat_2(A_1) | ~v1_relat_2(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.33  tff(c_116, plain, (v2_wellord1('#skF_2') | ~v1_wellord1('#skF_2') | ~v6_relat_2('#skF_2') | ~v4_relat_2('#skF_2') | ~v1_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_112, c_2])).
% 1.81/1.33  tff(c_119, plain, (v2_wellord1('#skF_2') | ~v6_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82, c_74, c_89, c_116])).
% 1.81/1.33  tff(c_120, plain, (~v6_relat_2('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_119])).
% 1.81/1.33  tff(c_97, plain, (![B_31, A_32, C_33]: (v6_relat_2(B_31) | ~v6_relat_2(A_32) | ~r3_wellord1(A_32, B_31, C_33) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_relat_1(B_31) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.81/1.33  tff(c_100, plain, (v6_relat_2('#skF_2') | ~v6_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_97])).
% 1.81/1.33  tff(c_103, plain, (v6_relat_2('#skF_2') | ~v6_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_100])).
% 1.81/1.33  tff(c_133, plain, (~v6_relat_2('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_120, c_103])).
% 1.81/1.33  tff(c_136, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_133])).
% 1.81/1.33  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_136])).
% 1.81/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.33  
% 1.81/1.33  Inference rules
% 1.81/1.33  ----------------------
% 1.81/1.33  #Ref     : 0
% 1.81/1.33  #Sup     : 14
% 1.81/1.33  #Fact    : 0
% 1.81/1.33  #Define  : 0
% 1.81/1.33  #Split   : 2
% 1.81/1.33  #Chain   : 0
% 1.81/1.33  #Close   : 0
% 1.81/1.33  
% 1.81/1.33  Ordering : KBO
% 1.81/1.33  
% 1.81/1.33  Simplification rules
% 1.81/1.33  ----------------------
% 1.81/1.33  #Subsume      : 1
% 1.81/1.33  #Demod        : 40
% 1.81/1.33  #Tautology    : 2
% 1.81/1.33  #SimpNegUnit  : 2
% 1.81/1.33  #BackRed      : 0
% 1.81/1.33  
% 1.81/1.33  #Partial instantiations: 0
% 1.81/1.33  #Strategies tried      : 1
% 1.81/1.33  
% 1.81/1.33  Timing (in seconds)
% 1.81/1.33  ----------------------
% 1.81/1.33  Preprocessing        : 0.30
% 1.81/1.33  Parsing              : 0.16
% 1.81/1.33  CNF conversion       : 0.02
% 1.81/1.33  Main loop            : 0.16
% 1.81/1.33  Inferencing          : 0.07
% 1.81/1.33  Reduction            : 0.05
% 2.07/1.33  Demodulation         : 0.03
% 2.07/1.33  BG Simplification    : 0.02
% 2.07/1.33  Subsumption          : 0.02
% 2.07/1.33  Abstraction          : 0.01
% 2.07/1.33  MUC search           : 0.00
% 2.07/1.33  Cooper               : 0.00
% 2.07/1.33  Total                : 0.50
% 2.07/1.33  Index Insertion      : 0.00
% 2.07/1.33  Index Deletion       : 0.00
% 2.07/1.33  Index Matching       : 0.00
% 2.07/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
