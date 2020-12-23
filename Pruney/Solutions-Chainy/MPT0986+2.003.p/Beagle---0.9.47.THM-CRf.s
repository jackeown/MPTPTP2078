%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:53 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    5
%              Number of atoms          :   59 ( 117 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    ! [C_12,A_13,B_14] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_relset_1(A_15,B_16,C_17) = k1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_60,plain,(
    ! [B_28,A_29,C_30] :
      ( k1_xboole_0 = B_28
      | k1_relset_1(A_29,B_28,C_30) = A_29
      | ~ v1_funct_2(C_30,A_29,B_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_29,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_63,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_63])).

tff(c_67,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_66])).

tff(c_77,plain,(
    ! [B_31,A_32] :
      ( k1_funct_1(k2_funct_1(B_31),k1_funct_1(B_31,A_32)) = A_32
      | ~ r2_hidden(A_32,k1_relat_1(B_31))
      | ~ v2_funct_1(B_31)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_86,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_22])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_34,c_28,c_26,c_67,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.14  
% 1.85/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.15  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.85/1.15  
% 1.85/1.15  %Foreground sorts:
% 1.85/1.15  
% 1.85/1.15  
% 1.85/1.15  %Background operators:
% 1.85/1.15  
% 1.85/1.15  
% 1.85/1.15  %Foreground operators:
% 1.85/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.85/1.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.85/1.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.85/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.85/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.85/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.85/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.85/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.85/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.15  
% 1.85/1.15  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 1.85/1.15  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.85/1.15  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.85/1.15  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.85/1.15  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 1.85/1.15  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.85/1.15  tff(c_35, plain, (![C_12, A_13, B_14]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.15  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_35])).
% 1.85/1.15  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.85/1.15  tff(c_28, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.85/1.15  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.85/1.15  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.85/1.15  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.85/1.15  tff(c_40, plain, (![A_15, B_16, C_17]: (k1_relset_1(A_15, B_16, C_17)=k1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.15  tff(c_44, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_40])).
% 1.85/1.15  tff(c_60, plain, (![B_28, A_29, C_30]: (k1_xboole_0=B_28 | k1_relset_1(A_29, B_28, C_30)=A_29 | ~v1_funct_2(C_30, A_29, B_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_29, B_28))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.85/1.15  tff(c_63, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_60])).
% 1.85/1.15  tff(c_66, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_63])).
% 1.85/1.15  tff(c_67, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_24, c_66])).
% 1.85/1.15  tff(c_77, plain, (![B_31, A_32]: (k1_funct_1(k2_funct_1(B_31), k1_funct_1(B_31, A_32))=A_32 | ~r2_hidden(A_32, k1_relat_1(B_31)) | ~v2_funct_1(B_31) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.15  tff(c_22, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.85/1.15  tff(c_86, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77, c_22])).
% 1.85/1.15  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_34, c_28, c_26, c_67, c_86])).
% 1.85/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.15  
% 1.85/1.15  Inference rules
% 1.85/1.15  ----------------------
% 1.85/1.15  #Ref     : 0
% 1.85/1.15  #Sup     : 15
% 1.85/1.15  #Fact    : 0
% 1.85/1.15  #Define  : 0
% 1.85/1.15  #Split   : 0
% 1.85/1.15  #Chain   : 0
% 1.85/1.15  #Close   : 0
% 1.85/1.15  
% 1.85/1.15  Ordering : KBO
% 1.85/1.16  
% 1.85/1.16  Simplification rules
% 1.85/1.16  ----------------------
% 1.85/1.16  #Subsume      : 0
% 1.85/1.16  #Demod        : 10
% 1.85/1.16  #Tautology    : 8
% 1.85/1.16  #SimpNegUnit  : 2
% 1.85/1.16  #BackRed      : 1
% 1.85/1.16  
% 1.85/1.16  #Partial instantiations: 0
% 1.85/1.16  #Strategies tried      : 1
% 1.85/1.16  
% 1.85/1.16  Timing (in seconds)
% 1.85/1.16  ----------------------
% 1.85/1.16  Preprocessing        : 0.29
% 1.85/1.16  Parsing              : 0.15
% 1.85/1.16  CNF conversion       : 0.02
% 1.85/1.16  Main loop            : 0.11
% 1.85/1.16  Inferencing          : 0.04
% 1.85/1.16  Reduction            : 0.04
% 1.85/1.16  Demodulation         : 0.03
% 1.85/1.16  BG Simplification    : 0.01
% 1.85/1.16  Subsumption          : 0.02
% 1.85/1.16  Abstraction          : 0.01
% 1.85/1.16  MUC search           : 0.00
% 1.85/1.16  Cooper               : 0.00
% 1.85/1.16  Total                : 0.43
% 1.85/1.16  Index Insertion      : 0.00
% 1.85/1.16  Index Deletion       : 0.00
% 1.85/1.16  Index Matching       : 0.00
% 1.85/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
