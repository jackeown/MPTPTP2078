%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:48 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 129 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_funct_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r4_wellord1(A,B)
             => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
               => r3_wellord1(B,A,k2_funct_1(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_wellord1)).

tff(c_16,plain,(
    ~ r4_wellord1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    r4_wellord1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_2,B_8] :
      ( v1_funct_1('#skF_1'(A_2,B_8))
      | ~ r4_wellord1(A_2,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_2,B_8] :
      ( v1_relat_1('#skF_1'(A_2,B_8))
      | ~ r4_wellord1(A_2,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_2,B_8] :
      ( r3_wellord1(A_2,B_8,'#skF_1'(A_2,B_8))
      | ~ r4_wellord1(A_2,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

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

tff(c_33,plain,(
    ! [B_31,A_32,C_33] :
      ( r3_wellord1(B_31,A_32,k2_funct_1(C_33))
      | ~ r3_wellord1(A_32,B_31,C_33)
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_2,B_8,C_11] :
      ( r4_wellord1(A_2,B_8)
      | ~ r3_wellord1(A_2,B_8,C_11)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [B_34,A_35,C_36] :
      ( r4_wellord1(B_34,A_35)
      | ~ v1_funct_1(k2_funct_1(C_36))
      | ~ v1_relat_1(k2_funct_1(C_36))
      | ~ r3_wellord1(A_35,B_34,C_36)
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_33,c_6])).

tff(c_42,plain,(
    ! [B_37,A_38,A_39] :
      ( r4_wellord1(B_37,A_38)
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ r3_wellord1(A_38,B_37,A_39)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_38)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_46,plain,(
    ! [B_40,A_41,A_42] :
      ( r4_wellord1(B_40,A_41)
      | ~ r3_wellord1(A_41,B_40,A_42)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_41)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_42])).

tff(c_55,plain,(
    ! [B_43,A_44] :
      ( r4_wellord1(B_43,A_44)
      | ~ v1_funct_1('#skF_1'(A_44,B_43))
      | ~ v1_relat_1('#skF_1'(A_44,B_43))
      | ~ r4_wellord1(A_44,B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_60,plain,(
    ! [B_45,A_46] :
      ( r4_wellord1(B_45,A_46)
      | ~ v1_funct_1('#skF_1'(A_46,B_45))
      | ~ r4_wellord1(A_46,B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_55])).

tff(c_65,plain,(
    ! [B_47,A_48] :
      ( r4_wellord1(B_47,A_48)
      | ~ r4_wellord1(A_48,B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_67,plain,
    ( r4_wellord1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_70,plain,(
    r4_wellord1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_67])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.18  
% 1.78/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.18  %$ r3_wellord1 > r4_wellord1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_funct_1 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.18  
% 1.78/1.18  %Foreground sorts:
% 1.78/1.18  
% 1.78/1.18  
% 1.78/1.18  %Background operators:
% 1.78/1.18  
% 1.78/1.18  
% 1.78/1.18  %Foreground operators:
% 1.78/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.78/1.18  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 1.78/1.18  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 1.78/1.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.18  
% 1.88/1.19  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 1.88/1.19  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) <=> (?[C]: ((v1_relat_1(C) & v1_funct_1(C)) & r3_wellord1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_wellord1)).
% 1.88/1.19  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.88/1.19  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) => r3_wellord1(B, A, k2_funct_1(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_wellord1)).
% 1.88/1.19  tff(c_16, plain, (~r4_wellord1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_18, plain, (r4_wellord1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.19  tff(c_10, plain, (![A_2, B_8]: (v1_funct_1('#skF_1'(A_2, B_8)) | ~r4_wellord1(A_2, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.19  tff(c_12, plain, (![A_2, B_8]: (v1_relat_1('#skF_1'(A_2, B_8)) | ~r4_wellord1(A_2, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.19  tff(c_8, plain, (![A_2, B_8]: (r3_wellord1(A_2, B_8, '#skF_1'(A_2, B_8)) | ~r4_wellord1(A_2, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.19  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.19  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.19  tff(c_33, plain, (![B_31, A_32, C_33]: (r3_wellord1(B_31, A_32, k2_funct_1(C_33)) | ~r3_wellord1(A_32, B_31, C_33) | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_relat_1(B_31) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.19  tff(c_6, plain, (![A_2, B_8, C_11]: (r4_wellord1(A_2, B_8) | ~r3_wellord1(A_2, B_8, C_11) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11) | ~v1_relat_1(B_8) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.19  tff(c_38, plain, (![B_34, A_35, C_36]: (r4_wellord1(B_34, A_35) | ~v1_funct_1(k2_funct_1(C_36)) | ~v1_relat_1(k2_funct_1(C_36)) | ~r3_wellord1(A_35, B_34, C_36) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36) | ~v1_relat_1(B_34) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_33, c_6])).
% 1.88/1.19  tff(c_42, plain, (![B_37, A_38, A_39]: (r4_wellord1(B_37, A_38) | ~v1_funct_1(k2_funct_1(A_39)) | ~r3_wellord1(A_38, B_37, A_39) | ~v1_relat_1(B_37) | ~v1_relat_1(A_38) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_4, c_38])).
% 1.88/1.19  tff(c_46, plain, (![B_40, A_41, A_42]: (r4_wellord1(B_40, A_41) | ~r3_wellord1(A_41, B_40, A_42) | ~v1_relat_1(B_40) | ~v1_relat_1(A_41) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_2, c_42])).
% 1.88/1.19  tff(c_55, plain, (![B_43, A_44]: (r4_wellord1(B_43, A_44) | ~v1_funct_1('#skF_1'(A_44, B_43)) | ~v1_relat_1('#skF_1'(A_44, B_43)) | ~r4_wellord1(A_44, B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_8, c_46])).
% 1.88/1.19  tff(c_60, plain, (![B_45, A_46]: (r4_wellord1(B_45, A_46) | ~v1_funct_1('#skF_1'(A_46, B_45)) | ~r4_wellord1(A_46, B_45) | ~v1_relat_1(B_45) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_12, c_55])).
% 1.88/1.19  tff(c_65, plain, (![B_47, A_48]: (r4_wellord1(B_47, A_48) | ~r4_wellord1(A_48, B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_10, c_60])).
% 1.88/1.19  tff(c_67, plain, (r4_wellord1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_65])).
% 1.88/1.19  tff(c_70, plain, (r4_wellord1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_67])).
% 1.88/1.19  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_70])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 9
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 0
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 5
% 1.88/1.19  #Demod        : 2
% 1.88/1.19  #Tautology    : 1
% 1.88/1.19  #SimpNegUnit  : 1
% 1.88/1.19  #BackRed      : 0
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.26
% 1.88/1.19  Parsing              : 0.14
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.13
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.03
% 1.88/1.19  Demodulation         : 0.02
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.03
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.41
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
