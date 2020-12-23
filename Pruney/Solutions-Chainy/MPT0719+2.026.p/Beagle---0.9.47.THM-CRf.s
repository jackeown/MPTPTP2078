%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:46 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 103 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_1 > #skF_2

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

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
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

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_25] : k2_zfmisc_1(A_25,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_8])).

tff(c_12,plain,(
    ! [A_4,B_5] : ~ r2_hidden(A_4,k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_102,plain,(
    ! [A_25] : ~ r2_hidden(A_25,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_12])).

tff(c_53,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_41,plain,(
    ! [A_18] :
      ( v1_funct_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_41])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_18])).

tff(c_144,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_2'(A_31,B_32),k1_relat_1(B_32))
      | v5_funct_1(B_32,A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_147,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_2'(A_31,'#skF_1'),'#skF_1')
      | v5_funct_1('#skF_1',A_31)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_144])).

tff(c_149,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_2'(A_31,'#skF_1'),'#skF_1')
      | v5_funct_1('#skF_1',A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_45,c_147])).

tff(c_151,plain,(
    ! [A_33] :
      ( v5_funct_1('#skF_1',A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_149])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_81,plain,(
    ~ v5_funct_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_28])).

tff(c_154,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_151,c_81])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:46:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_1 > #skF_2
% 1.83/1.17  
% 1.83/1.17  %Foreground sorts:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Background operators:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Foreground operators:
% 1.83/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.17  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.83/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.17  
% 1.83/1.18  tff(f_74, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.83/1.18  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.83/1.18  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.83/1.18  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.83/1.18  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.83/1.18  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.83/1.18  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.83/1.18  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.83/1.18  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.83/1.18  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.83/1.18  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.83/1.18  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.18  tff(c_73, plain, (![A_22]: (k1_xboole_0=A_22 | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_77, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_73])).
% 1.83/1.18  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.18  tff(c_97, plain, (![A_25]: (k2_zfmisc_1(A_25, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_8])).
% 1.83/1.18  tff(c_12, plain, (![A_4, B_5]: (~r2_hidden(A_4, k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.18  tff(c_102, plain, (![A_25]: (~r2_hidden(A_25, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_12])).
% 1.83/1.18  tff(c_53, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.18  tff(c_57, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_53])).
% 1.83/1.18  tff(c_41, plain, (![A_18]: (v1_funct_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.83/1.18  tff(c_45, plain, (v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_41])).
% 1.83/1.18  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.83/1.18  tff(c_83, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_18])).
% 1.83/1.18  tff(c_144, plain, (![A_31, B_32]: (r2_hidden('#skF_2'(A_31, B_32), k1_relat_1(B_32)) | v5_funct_1(B_32, A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.83/1.18  tff(c_147, plain, (![A_31]: (r2_hidden('#skF_2'(A_31, '#skF_1'), '#skF_1') | v5_funct_1('#skF_1', A_31) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_83, c_144])).
% 1.83/1.18  tff(c_149, plain, (![A_31]: (r2_hidden('#skF_2'(A_31, '#skF_1'), '#skF_1') | v5_funct_1('#skF_1', A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_45, c_147])).
% 1.83/1.18  tff(c_151, plain, (![A_33]: (v5_funct_1('#skF_1', A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(negUnitSimplification, [status(thm)], [c_102, c_149])).
% 1.83/1.18  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.83/1.18  tff(c_81, plain, (~v5_funct_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_28])).
% 1.83/1.18  tff(c_154, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_151, c_81])).
% 1.83/1.18  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_154])).
% 1.83/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  Inference rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Ref     : 0
% 1.83/1.18  #Sup     : 32
% 1.83/1.18  #Fact    : 0
% 1.83/1.18  #Define  : 0
% 1.83/1.18  #Split   : 0
% 1.83/1.18  #Chain   : 0
% 1.83/1.18  #Close   : 0
% 1.83/1.18  
% 1.83/1.18  Ordering : KBO
% 1.83/1.18  
% 1.83/1.18  Simplification rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Subsume      : 1
% 1.83/1.18  #Demod        : 17
% 1.83/1.18  #Tautology    : 25
% 1.83/1.18  #SimpNegUnit  : 1
% 1.83/1.18  #BackRed      : 6
% 1.83/1.18  
% 1.83/1.18  #Partial instantiations: 0
% 1.83/1.18  #Strategies tried      : 1
% 1.83/1.18  
% 1.83/1.18  Timing (in seconds)
% 1.83/1.18  ----------------------
% 1.83/1.19  Preprocessing        : 0.28
% 1.83/1.19  Parsing              : 0.16
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.13
% 1.83/1.19  Inferencing          : 0.05
% 1.83/1.19  Reduction            : 0.04
% 1.83/1.19  Demodulation         : 0.03
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.43
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
