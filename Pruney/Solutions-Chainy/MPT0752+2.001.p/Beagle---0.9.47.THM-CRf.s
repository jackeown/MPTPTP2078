%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:26 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   42 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 (  85 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v5_ordinal1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_22,plain,(
    ! [A_12] : v1_relat_1('#skF_1'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_12] : v5_relat_1('#skF_1'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_59,plain,(
    ! [C_28,A_29,B_30] :
      ( v5_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(B_30))
      | ~ v5_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_31,A_32] :
      ( v5_relat_1(k1_xboole_0,A_31)
      | ~ v5_relat_1(A_32,A_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_65,plain,(
    ! [A_12] :
      ( v5_relat_1(k1_xboole_0,A_12)
      | ~ v1_relat_1('#skF_1'(A_12)) ) ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_68,plain,(
    ! [A_12] : v5_relat_1(k1_xboole_0,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_65])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    ! [A_20] :
      ( v5_ordinal1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_19] :
      ( v1_funct_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_29,plain,(
    ! [A_18] :
      ( v1_relat_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

tff(c_24,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_2')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,
    ( ~ v5_relat_1(k1_xboole_0,'#skF_2')
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_33,c_24])).

tff(c_41,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_45,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_41])).

tff(c_49,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_50,plain,(
    ~ v5_relat_1(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  %$ v5_relat_1 > r2_hidden > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.11  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.66/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.66/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.11  
% 1.66/1.12  tff(f_64, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_ordinal1)).
% 1.66/1.12  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.66/1.12  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 1.66/1.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.66/1.12  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.66/1.12  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.66/1.12  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.66/1.12  tff(f_73, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.66/1.12  tff(c_22, plain, (![A_12]: (v1_relat_1('#skF_1'(A_12)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.66/1.12  tff(c_20, plain, (![A_12]: (v5_relat_1('#skF_1'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.66/1.12  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.66/1.12  tff(c_59, plain, (![C_28, A_29, B_30]: (v5_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(B_30)) | ~v5_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.12  tff(c_63, plain, (![A_31, A_32]: (v5_relat_1(k1_xboole_0, A_31) | ~v5_relat_1(A_32, A_31) | ~v1_relat_1(A_32))), inference(resolution, [status(thm)], [c_4, c_59])).
% 1.66/1.12  tff(c_65, plain, (![A_12]: (v5_relat_1(k1_xboole_0, A_12) | ~v1_relat_1('#skF_1'(A_12)))), inference(resolution, [status(thm)], [c_20, c_63])).
% 1.66/1.12  tff(c_68, plain, (![A_12]: (v5_relat_1(k1_xboole_0, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_65])).
% 1.66/1.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.66/1.12  tff(c_42, plain, (![A_20]: (v5_ordinal1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.66/1.12  tff(c_34, plain, (![A_19]: (v1_funct_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.66/1.12  tff(c_38, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_34])).
% 1.66/1.12  tff(c_29, plain, (![A_18]: (v1_relat_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.12  tff(c_33, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_29])).
% 1.66/1.12  tff(c_24, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_2') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.66/1.12  tff(c_40, plain, (~v5_relat_1(k1_xboole_0, '#skF_2') | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_33, c_24])).
% 1.66/1.12  tff(c_41, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_40])).
% 1.66/1.12  tff(c_45, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_41])).
% 1.66/1.12  tff(c_49, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_45])).
% 1.66/1.12  tff(c_50, plain, (~v5_relat_1(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 1.66/1.12  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_50])).
% 1.66/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  Inference rules
% 1.66/1.12  ----------------------
% 1.66/1.13  #Ref     : 0
% 1.66/1.13  #Sup     : 6
% 1.66/1.13  #Fact    : 0
% 1.66/1.13  #Define  : 0
% 1.66/1.13  #Split   : 1
% 1.66/1.13  #Chain   : 0
% 1.66/1.13  #Close   : 0
% 1.66/1.13  
% 1.66/1.13  Ordering : KBO
% 1.66/1.13  
% 1.66/1.13  Simplification rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Subsume      : 0
% 1.66/1.13  #Demod        : 6
% 1.66/1.13  #Tautology    : 1
% 1.66/1.13  #SimpNegUnit  : 0
% 1.66/1.13  #BackRed      : 1
% 1.66/1.13  
% 1.66/1.13  #Partial instantiations: 0
% 1.66/1.13  #Strategies tried      : 1
% 1.66/1.13  
% 1.66/1.13  Timing (in seconds)
% 1.66/1.13  ----------------------
% 1.66/1.13  Preprocessing        : 0.26
% 1.66/1.13  Parsing              : 0.15
% 1.66/1.13  CNF conversion       : 0.02
% 1.66/1.13  Main loop            : 0.11
% 1.66/1.13  Inferencing          : 0.05
% 1.66/1.13  Reduction            : 0.03
% 1.66/1.13  Demodulation         : 0.02
% 1.66/1.13  BG Simplification    : 0.01
% 1.66/1.13  Subsumption          : 0.01
% 1.66/1.13  Abstraction          : 0.00
% 1.66/1.13  MUC search           : 0.00
% 1.66/1.13  Cooper               : 0.00
% 1.66/1.13  Total                : 0.40
% 1.66/1.13  Index Insertion      : 0.00
% 1.66/1.13  Index Deletion       : 0.00
% 1.66/1.13  Index Matching       : 0.00
% 1.66/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
