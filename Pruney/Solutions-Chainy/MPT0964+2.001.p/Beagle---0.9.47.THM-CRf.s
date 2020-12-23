%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:59 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 124 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_58,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_155,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_169,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_329,plain,(
    ! [B_156,A_157,C_158] :
      ( k1_xboole_0 = B_156
      | k1_relset_1(A_157,B_156,C_158) = A_157
      | ~ v1_funct_2(C_158,A_157,B_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_340,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_329])).

tff(c_345,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_169,c_340])).

tff(c_346,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_345])).

tff(c_96,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_105,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_96])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_232,plain,(
    ! [A_143,C_144] :
      ( r2_hidden(k4_tarski(A_143,k1_funct_1(C_144,A_143)),C_144)
      | ~ r2_hidden(A_143,k1_relat_1(C_144))
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [B_23,C_24,A_22] :
      ( r2_hidden(B_23,k2_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_285,plain,(
    ! [C_147,A_148] :
      ( r2_hidden(k1_funct_1(C_147,A_148),k2_relat_1(C_147))
      | ~ r2_hidden(A_148,k1_relat_1(C_147))
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_232,c_20])).

tff(c_174,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relset_1(A_122,B_123,C_124) = k2_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_188,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_174])).

tff(c_54,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_6'),k2_relset_1('#skF_4','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_189,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_54])).

tff(c_288,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_285,c_189])).

tff(c_297,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_64,c_288])).

tff(c_347,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_297])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.49  
% 2.65/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.49  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 2.65/1.49  
% 2.65/1.49  %Foreground sorts:
% 2.65/1.49  
% 2.65/1.49  
% 2.65/1.49  %Background operators:
% 2.65/1.49  
% 2.65/1.49  
% 2.65/1.49  %Foreground operators:
% 2.65/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.65/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.65/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.65/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.65/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.65/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.65/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.49  
% 2.85/1.51  tff(f_149, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.85/1.51  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.85/1.51  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.85/1.51  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.85/1.51  tff(f_86, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.85/1.51  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.85/1.51  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.85/1.51  tff(c_58, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.85/1.51  tff(c_56, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.85/1.51  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.85/1.51  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.85/1.51  tff(c_155, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.85/1.51  tff(c_169, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_155])).
% 2.85/1.51  tff(c_329, plain, (![B_156, A_157, C_158]: (k1_xboole_0=B_156 | k1_relset_1(A_157, B_156, C_158)=A_157 | ~v1_funct_2(C_158, A_157, B_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.85/1.51  tff(c_340, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_329])).
% 2.85/1.51  tff(c_345, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_169, c_340])).
% 2.85/1.51  tff(c_346, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_345])).
% 2.85/1.51  tff(c_96, plain, (![C_97, A_98, B_99]: (v1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.85/1.51  tff(c_105, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_96])).
% 2.85/1.51  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.85/1.51  tff(c_232, plain, (![A_143, C_144]: (r2_hidden(k4_tarski(A_143, k1_funct_1(C_144, A_143)), C_144) | ~r2_hidden(A_143, k1_relat_1(C_144)) | ~v1_funct_1(C_144) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.51  tff(c_20, plain, (![B_23, C_24, A_22]: (r2_hidden(B_23, k2_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.85/1.51  tff(c_285, plain, (![C_147, A_148]: (r2_hidden(k1_funct_1(C_147, A_148), k2_relat_1(C_147)) | ~r2_hidden(A_148, k1_relat_1(C_147)) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_232, c_20])).
% 2.85/1.51  tff(c_174, plain, (![A_122, B_123, C_124]: (k2_relset_1(A_122, B_123, C_124)=k2_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.85/1.51  tff(c_188, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_174])).
% 2.85/1.51  tff(c_54, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k2_relset_1('#skF_4', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.85/1.51  tff(c_189, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_54])).
% 2.85/1.51  tff(c_288, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_285, c_189])).
% 2.85/1.51  tff(c_297, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_64, c_288])).
% 2.85/1.51  tff(c_347, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_297])).
% 2.85/1.51  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_347])).
% 2.85/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.51  
% 2.85/1.51  Inference rules
% 2.85/1.51  ----------------------
% 2.85/1.51  #Ref     : 0
% 2.85/1.51  #Sup     : 55
% 2.85/1.51  #Fact    : 0
% 2.85/1.51  #Define  : 0
% 2.85/1.51  #Split   : 1
% 2.85/1.51  #Chain   : 0
% 2.85/1.51  #Close   : 0
% 2.85/1.51  
% 2.85/1.51  Ordering : KBO
% 2.85/1.51  
% 2.85/1.51  Simplification rules
% 2.85/1.51  ----------------------
% 2.85/1.51  #Subsume      : 8
% 2.85/1.51  #Demod        : 8
% 2.85/1.51  #Tautology    : 7
% 2.85/1.51  #SimpNegUnit  : 1
% 2.85/1.51  #BackRed      : 3
% 2.85/1.51  
% 2.85/1.51  #Partial instantiations: 0
% 2.85/1.51  #Strategies tried      : 1
% 2.85/1.51  
% 2.85/1.51  Timing (in seconds)
% 2.85/1.51  ----------------------
% 2.85/1.51  Preprocessing        : 0.34
% 2.85/1.51  Parsing              : 0.18
% 2.85/1.51  CNF conversion       : 0.03
% 2.85/1.51  Main loop            : 0.34
% 2.85/1.51  Inferencing          : 0.12
% 2.85/1.51  Reduction            : 0.09
% 2.85/1.51  Demodulation         : 0.07
% 2.85/1.51  BG Simplification    : 0.02
% 2.85/1.51  Subsumption          : 0.08
% 2.85/1.51  Abstraction          : 0.01
% 2.85/1.51  MUC search           : 0.00
% 2.85/1.51  Cooper               : 0.00
% 2.85/1.51  Total                : 0.71
% 2.85/1.51  Index Insertion      : 0.00
% 2.85/1.51  Index Deletion       : 0.00
% 2.85/1.51  Index Matching       : 0.00
% 2.85/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
