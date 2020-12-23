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
% DateTime   : Thu Dec  3 10:06:49 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 ( 251 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( ( r4_wellord1(A,B)
                    & r4_wellord1(B,C) )
                 => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( ( v1_relat_1(D)
                    & v1_funct_1(D) )
                 => ! [E] :
                      ( ( v1_relat_1(E)
                        & v1_funct_1(E) )
                     => ( ( r3_wellord1(A,B,D)
                          & r3_wellord1(B,C,E) )
                       => r3_wellord1(A,C,k5_relat_1(D,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_wellord1)).

tff(c_16,plain,(
    ~ r4_wellord1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    r4_wellord1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    r4_wellord1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_3,B_9] :
      ( v1_funct_1('#skF_1'(A_3,B_9))
      | ~ r4_wellord1(A_3,B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_3,B_9] :
      ( v1_relat_1('#skF_1'(A_3,B_9))
      | ~ r4_wellord1(A_3,B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3,B_9] :
      ( r3_wellord1(A_3,B_9,'#skF_1'(A_3,B_9))
      | ~ r4_wellord1(A_3,B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_funct_1(k5_relat_1(A_1,B_2))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [B_63,E_65,D_64,C_61,A_62] :
      ( r3_wellord1(A_62,C_61,k5_relat_1(D_64,E_65))
      | ~ r3_wellord1(B_63,C_61,E_65)
      | ~ r3_wellord1(A_62,B_63,D_64)
      | ~ v1_funct_1(E_65)
      | ~ v1_relat_1(E_65)
      | ~ v1_funct_1(D_64)
      | ~ v1_relat_1(D_64)
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41,plain,(
    ! [A_66,B_67,D_68,A_69] :
      ( r3_wellord1(A_66,B_67,k5_relat_1(D_68,'#skF_1'(A_69,B_67)))
      | ~ r3_wellord1(A_66,A_69,D_68)
      | ~ v1_funct_1('#skF_1'(A_69,B_67))
      | ~ v1_relat_1('#skF_1'(A_69,B_67))
      | ~ v1_funct_1(D_68)
      | ~ v1_relat_1(D_68)
      | ~ v1_relat_1(A_66)
      | ~ r4_wellord1(A_69,B_67)
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_8,c_37])).

tff(c_6,plain,(
    ! [A_3,B_9,C_12] :
      ( r4_wellord1(A_3,B_9)
      | ~ r3_wellord1(A_3,B_9,C_12)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [A_70,B_71,D_72,A_73] :
      ( r4_wellord1(A_70,B_71)
      | ~ v1_funct_1(k5_relat_1(D_72,'#skF_1'(A_73,B_71)))
      | ~ v1_relat_1(k5_relat_1(D_72,'#skF_1'(A_73,B_71)))
      | ~ r3_wellord1(A_70,A_73,D_72)
      | ~ v1_funct_1('#skF_1'(A_73,B_71))
      | ~ v1_relat_1('#skF_1'(A_73,B_71))
      | ~ v1_funct_1(D_72)
      | ~ v1_relat_1(D_72)
      | ~ v1_relat_1(A_70)
      | ~ r4_wellord1(A_73,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_41,c_6])).

tff(c_61,plain,(
    ! [A_80,B_81,A_82,A_83] :
      ( r4_wellord1(A_80,B_81)
      | ~ v1_funct_1(k5_relat_1(A_82,'#skF_1'(A_83,B_81)))
      | ~ r3_wellord1(A_80,A_83,A_82)
      | ~ v1_relat_1(A_80)
      | ~ r4_wellord1(A_83,B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_83)
      | ~ v1_funct_1('#skF_1'(A_83,B_81))
      | ~ v1_relat_1('#skF_1'(A_83,B_81))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_66,plain,(
    ! [A_84,B_85,A_86,A_87] :
      ( r4_wellord1(A_84,B_85)
      | ~ r3_wellord1(A_84,A_86,A_87)
      | ~ v1_relat_1(A_84)
      | ~ r4_wellord1(A_86,B_85)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_86)
      | ~ v1_funct_1('#skF_1'(A_86,B_85))
      | ~ v1_relat_1('#skF_1'(A_86,B_85))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_73,plain,(
    ! [A_88,B_89,B_90] :
      ( r4_wellord1(A_88,B_89)
      | ~ r4_wellord1(B_90,B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_funct_1('#skF_1'(B_90,B_89))
      | ~ v1_relat_1('#skF_1'(B_90,B_89))
      | ~ v1_funct_1('#skF_1'(A_88,B_90))
      | ~ v1_relat_1('#skF_1'(A_88,B_90))
      | ~ r4_wellord1(A_88,B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_77,plain,(
    ! [A_91,B_92,A_93] :
      ( r4_wellord1(A_91,B_92)
      | ~ v1_funct_1('#skF_1'(A_93,B_92))
      | ~ v1_funct_1('#skF_1'(A_91,A_93))
      | ~ v1_relat_1('#skF_1'(A_91,A_93))
      | ~ r4_wellord1(A_91,A_93)
      | ~ v1_relat_1(A_91)
      | ~ r4_wellord1(A_93,B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_12,c_73])).

tff(c_81,plain,(
    ! [A_94,B_95,A_96] :
      ( r4_wellord1(A_94,B_95)
      | ~ v1_funct_1('#skF_1'(A_94,A_96))
      | ~ v1_relat_1('#skF_1'(A_94,A_96))
      | ~ r4_wellord1(A_94,A_96)
      | ~ v1_relat_1(A_94)
      | ~ r4_wellord1(A_96,B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_85,plain,(
    ! [A_97,B_98,B_99] :
      ( r4_wellord1(A_97,B_98)
      | ~ v1_funct_1('#skF_1'(A_97,B_99))
      | ~ r4_wellord1(B_99,B_98)
      | ~ v1_relat_1(B_98)
      | ~ r4_wellord1(A_97,B_99)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_12,c_81])).

tff(c_89,plain,(
    ! [A_100,B_101,B_102] :
      ( r4_wellord1(A_100,B_101)
      | ~ r4_wellord1(B_102,B_101)
      | ~ v1_relat_1(B_101)
      | ~ r4_wellord1(A_100,B_102)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_91,plain,(
    ! [A_100] :
      ( r4_wellord1(A_100,'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r4_wellord1(A_100,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_18,c_89])).

tff(c_100,plain,(
    ! [A_103] :
      ( r4_wellord1(A_103,'#skF_4')
      | ~ r4_wellord1(A_103,'#skF_3')
      | ~ v1_relat_1(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_91])).

tff(c_103,plain,
    ( r4_wellord1('#skF_2','#skF_4')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_106,plain,(
    r4_wellord1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_103])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.24  
% 2.39/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.24  %$ r3_wellord1 > r4_wellord1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.39/1.24  
% 2.39/1.24  %Foreground sorts:
% 2.39/1.24  
% 2.39/1.24  
% 2.39/1.24  %Background operators:
% 2.39/1.24  
% 2.39/1.24  
% 2.39/1.24  %Foreground operators:
% 2.39/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.24  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.39/1.24  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 2.39/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.39/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.24  
% 2.39/1.26  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r4_wellord1(A, B) & r4_wellord1(B, C)) => r4_wellord1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_wellord1)).
% 2.39/1.26  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) <=> (?[C]: ((v1_relat_1(C) & v1_funct_1(C)) & r3_wellord1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_wellord1)).
% 2.39/1.26  tff(f_37, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.39/1.26  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => ((r3_wellord1(A, B, D) & r3_wellord1(B, C, E)) => r3_wellord1(A, C, k5_relat_1(D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_wellord1)).
% 2.39/1.26  tff(c_16, plain, (~r4_wellord1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.26  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.26  tff(c_20, plain, (r4_wellord1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.26  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.26  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.26  tff(c_18, plain, (r4_wellord1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.26  tff(c_10, plain, (![A_3, B_9]: (v1_funct_1('#skF_1'(A_3, B_9)) | ~r4_wellord1(A_3, B_9) | ~v1_relat_1(B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.26  tff(c_12, plain, (![A_3, B_9]: (v1_relat_1('#skF_1'(A_3, B_9)) | ~r4_wellord1(A_3, B_9) | ~v1_relat_1(B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.26  tff(c_8, plain, (![A_3, B_9]: (r3_wellord1(A_3, B_9, '#skF_1'(A_3, B_9)) | ~r4_wellord1(A_3, B_9) | ~v1_relat_1(B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.26  tff(c_2, plain, (![A_1, B_2]: (v1_funct_1(k5_relat_1(A_1, B_2)) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.39/1.26  tff(c_4, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.39/1.26  tff(c_37, plain, (![B_63, E_65, D_64, C_61, A_62]: (r3_wellord1(A_62, C_61, k5_relat_1(D_64, E_65)) | ~r3_wellord1(B_63, C_61, E_65) | ~r3_wellord1(A_62, B_63, D_64) | ~v1_funct_1(E_65) | ~v1_relat_1(E_65) | ~v1_funct_1(D_64) | ~v1_relat_1(D_64) | ~v1_relat_1(C_61) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.26  tff(c_41, plain, (![A_66, B_67, D_68, A_69]: (r3_wellord1(A_66, B_67, k5_relat_1(D_68, '#skF_1'(A_69, B_67))) | ~r3_wellord1(A_66, A_69, D_68) | ~v1_funct_1('#skF_1'(A_69, B_67)) | ~v1_relat_1('#skF_1'(A_69, B_67)) | ~v1_funct_1(D_68) | ~v1_relat_1(D_68) | ~v1_relat_1(A_66) | ~r4_wellord1(A_69, B_67) | ~v1_relat_1(B_67) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_8, c_37])).
% 2.39/1.26  tff(c_6, plain, (![A_3, B_9, C_12]: (r4_wellord1(A_3, B_9) | ~r3_wellord1(A_3, B_9, C_12) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(B_9) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.26  tff(c_49, plain, (![A_70, B_71, D_72, A_73]: (r4_wellord1(A_70, B_71) | ~v1_funct_1(k5_relat_1(D_72, '#skF_1'(A_73, B_71))) | ~v1_relat_1(k5_relat_1(D_72, '#skF_1'(A_73, B_71))) | ~r3_wellord1(A_70, A_73, D_72) | ~v1_funct_1('#skF_1'(A_73, B_71)) | ~v1_relat_1('#skF_1'(A_73, B_71)) | ~v1_funct_1(D_72) | ~v1_relat_1(D_72) | ~v1_relat_1(A_70) | ~r4_wellord1(A_73, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_41, c_6])).
% 2.39/1.26  tff(c_61, plain, (![A_80, B_81, A_82, A_83]: (r4_wellord1(A_80, B_81) | ~v1_funct_1(k5_relat_1(A_82, '#skF_1'(A_83, B_81))) | ~r3_wellord1(A_80, A_83, A_82) | ~v1_relat_1(A_80) | ~r4_wellord1(A_83, B_81) | ~v1_relat_1(B_81) | ~v1_relat_1(A_83) | ~v1_funct_1('#skF_1'(A_83, B_81)) | ~v1_relat_1('#skF_1'(A_83, B_81)) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_4, c_49])).
% 2.39/1.26  tff(c_66, plain, (![A_84, B_85, A_86, A_87]: (r4_wellord1(A_84, B_85) | ~r3_wellord1(A_84, A_86, A_87) | ~v1_relat_1(A_84) | ~r4_wellord1(A_86, B_85) | ~v1_relat_1(B_85) | ~v1_relat_1(A_86) | ~v1_funct_1('#skF_1'(A_86, B_85)) | ~v1_relat_1('#skF_1'(A_86, B_85)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_2, c_61])).
% 2.39/1.26  tff(c_73, plain, (![A_88, B_89, B_90]: (r4_wellord1(A_88, B_89) | ~r4_wellord1(B_90, B_89) | ~v1_relat_1(B_89) | ~v1_funct_1('#skF_1'(B_90, B_89)) | ~v1_relat_1('#skF_1'(B_90, B_89)) | ~v1_funct_1('#skF_1'(A_88, B_90)) | ~v1_relat_1('#skF_1'(A_88, B_90)) | ~r4_wellord1(A_88, B_90) | ~v1_relat_1(B_90) | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_8, c_66])).
% 2.39/1.26  tff(c_77, plain, (![A_91, B_92, A_93]: (r4_wellord1(A_91, B_92) | ~v1_funct_1('#skF_1'(A_93, B_92)) | ~v1_funct_1('#skF_1'(A_91, A_93)) | ~v1_relat_1('#skF_1'(A_91, A_93)) | ~r4_wellord1(A_91, A_93) | ~v1_relat_1(A_91) | ~r4_wellord1(A_93, B_92) | ~v1_relat_1(B_92) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_12, c_73])).
% 2.39/1.26  tff(c_81, plain, (![A_94, B_95, A_96]: (r4_wellord1(A_94, B_95) | ~v1_funct_1('#skF_1'(A_94, A_96)) | ~v1_relat_1('#skF_1'(A_94, A_96)) | ~r4_wellord1(A_94, A_96) | ~v1_relat_1(A_94) | ~r4_wellord1(A_96, B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_10, c_77])).
% 2.39/1.26  tff(c_85, plain, (![A_97, B_98, B_99]: (r4_wellord1(A_97, B_98) | ~v1_funct_1('#skF_1'(A_97, B_99)) | ~r4_wellord1(B_99, B_98) | ~v1_relat_1(B_98) | ~r4_wellord1(A_97, B_99) | ~v1_relat_1(B_99) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_12, c_81])).
% 2.39/1.26  tff(c_89, plain, (![A_100, B_101, B_102]: (r4_wellord1(A_100, B_101) | ~r4_wellord1(B_102, B_101) | ~v1_relat_1(B_101) | ~r4_wellord1(A_100, B_102) | ~v1_relat_1(B_102) | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_10, c_85])).
% 2.39/1.26  tff(c_91, plain, (![A_100]: (r4_wellord1(A_100, '#skF_4') | ~v1_relat_1('#skF_4') | ~r4_wellord1(A_100, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_18, c_89])).
% 2.39/1.26  tff(c_100, plain, (![A_103]: (r4_wellord1(A_103, '#skF_4') | ~r4_wellord1(A_103, '#skF_3') | ~v1_relat_1(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_91])).
% 2.39/1.26  tff(c_103, plain, (r4_wellord1('#skF_2', '#skF_4') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_100])).
% 2.39/1.26  tff(c_106, plain, (r4_wellord1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_103])).
% 2.39/1.26  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_106])).
% 2.39/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.26  
% 2.39/1.26  Inference rules
% 2.39/1.26  ----------------------
% 2.39/1.26  #Ref     : 0
% 2.39/1.26  #Sup     : 17
% 2.39/1.26  #Fact    : 0
% 2.39/1.26  #Define  : 0
% 2.39/1.26  #Split   : 0
% 2.39/1.26  #Chain   : 0
% 2.39/1.26  #Close   : 0
% 2.39/1.26  
% 2.39/1.26  Ordering : KBO
% 2.39/1.26  
% 2.39/1.26  Simplification rules
% 2.39/1.26  ----------------------
% 2.39/1.26  #Subsume      : 6
% 2.39/1.26  #Demod        : 5
% 2.39/1.26  #Tautology    : 1
% 2.39/1.26  #SimpNegUnit  : 1
% 2.39/1.26  #BackRed      : 0
% 2.39/1.26  
% 2.39/1.26  #Partial instantiations: 0
% 2.39/1.26  #Strategies tried      : 1
% 2.39/1.26  
% 2.39/1.26  Timing (in seconds)
% 2.39/1.26  ----------------------
% 2.39/1.26  Preprocessing        : 0.28
% 2.39/1.26  Parsing              : 0.15
% 2.39/1.26  CNF conversion       : 0.02
% 2.39/1.26  Main loop            : 0.20
% 2.39/1.26  Inferencing          : 0.09
% 2.39/1.26  Reduction            : 0.04
% 2.39/1.26  Demodulation         : 0.03
% 2.39/1.26  BG Simplification    : 0.02
% 2.39/1.26  Subsumption          : 0.05
% 2.39/1.26  Abstraction          : 0.01
% 2.39/1.26  MUC search           : 0.00
% 2.39/1.26  Cooper               : 0.00
% 2.39/1.26  Total                : 0.51
% 2.39/1.26  Index Insertion      : 0.00
% 2.39/1.26  Index Deletion       : 0.00
% 2.39/1.26  Index Matching       : 0.00
% 2.39/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
