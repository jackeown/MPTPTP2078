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
% DateTime   : Thu Dec  3 10:16:47 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 873 expanded)
%              Number of leaves         :   27 ( 331 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 (2827 expanded)
%              Number of equality atoms :   42 ( 938 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_83,axiom,(
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

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40])).

tff(c_42,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_199,plain,(
    ! [B_60,C_61,A_62] :
      ( k1_xboole_0 = B_60
      | v1_funct_2(C_61,A_62,B_60)
      | k1_relset_1(A_62,B_60,C_61) != A_62
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_202,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_199])).

tff(c_215,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_202])).

tff(c_216,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_215])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_26] :
      ( v1_funct_2(k1_xboole_0,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    ! [A_26] :
      ( v1_funct_2(k1_xboole_0,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_28])).

tff(c_326,plain,(
    ! [A_79] :
      ( v1_funct_2('#skF_4',A_79,'#skF_4')
      | A_79 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_216,c_50])).

tff(c_14,plain,(
    ! [A_8] : k9_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_231,plain,(
    ! [A_8] : k9_relat_1('#skF_4',A_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_14])).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_235,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_16])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_230,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_6])).

tff(c_106,plain,(
    ! [A_39,B_40] :
      ( k9_relat_1(k6_relat_1(A_39),B_40) = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_3','#skF_4')),'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_106])).

tff(c_279,plain,(
    k9_relat_1(k6_relat_1('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_113])).

tff(c_281,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_235,c_279])).

tff(c_300,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_48])).

tff(c_330,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_326,c_300])).

tff(c_299,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_42])).

tff(c_347,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_330,c_299])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_177,plain,(
    ! [C_57,B_58] :
      ( v1_funct_2(C_57,k1_xboole_0,B_58)
      | k1_relset_1(k1_xboole_0,B_58,C_57) != k1_xboole_0
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_181,plain,(
    ! [B_58] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_58)
      | k1_relset_1(k1_xboole_0,B_58,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_177])).

tff(c_373,plain,(
    ! [B_86] :
      ( v1_funct_2('#skF_4','#skF_4',B_86)
      | k1_relset_1('#skF_4',B_86,'#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_216,c_216,c_216,c_181])).

tff(c_348,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_300])).

tff(c_376,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_373,c_348])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.28/1.28  
% 2.28/1.28  %Foreground sorts:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Background operators:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Foreground operators:
% 2.28/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.28/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.28/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.28/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.28/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.28  
% 2.28/1.30  tff(f_96, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.28/1.30  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.28/1.30  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.28/1.30  tff(f_43, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.28/1.30  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.28/1.30  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.28/1.30  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.28/1.30  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.30  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.30  tff(c_40, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.30  tff(c_48, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40])).
% 2.28/1.30  tff(c_42, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.30  tff(c_199, plain, (![B_60, C_61, A_62]: (k1_xboole_0=B_60 | v1_funct_2(C_61, A_62, B_60) | k1_relset_1(A_62, B_60, C_61)!=A_62 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_60))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.28/1.30  tff(c_202, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_44, c_199])).
% 2.28/1.30  tff(c_215, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_202])).
% 2.28/1.30  tff(c_216, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_215])).
% 2.28/1.30  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.30  tff(c_28, plain, (![A_26]: (v1_funct_2(k1_xboole_0, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.28/1.30  tff(c_50, plain, (![A_26]: (v1_funct_2(k1_xboole_0, A_26, k1_xboole_0) | k1_xboole_0=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_28])).
% 2.28/1.30  tff(c_326, plain, (![A_79]: (v1_funct_2('#skF_4', A_79, '#skF_4') | A_79='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_216, c_50])).
% 2.28/1.30  tff(c_14, plain, (![A_8]: (k9_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.30  tff(c_231, plain, (![A_8]: (k9_relat_1('#skF_4', A_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_14])).
% 2.28/1.30  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.30  tff(c_235, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_16])).
% 2.28/1.30  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.30  tff(c_230, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_6])).
% 2.28/1.30  tff(c_106, plain, (![A_39, B_40]: (k9_relat_1(k6_relat_1(A_39), B_40)=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.30  tff(c_113, plain, (k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')), '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_106])).
% 2.28/1.30  tff(c_279, plain, (k9_relat_1(k6_relat_1('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_113])).
% 2.28/1.30  tff(c_281, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_231, c_235, c_279])).
% 2.28/1.30  tff(c_300, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_48])).
% 2.28/1.30  tff(c_330, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_326, c_300])).
% 2.28/1.30  tff(c_299, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_42])).
% 2.28/1.30  tff(c_347, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_330, c_330, c_299])).
% 2.28/1.30  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.30  tff(c_32, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.28/1.30  tff(c_177, plain, (![C_57, B_58]: (v1_funct_2(C_57, k1_xboole_0, B_58) | k1_relset_1(k1_xboole_0, B_58, C_57)!=k1_xboole_0 | ~m1_subset_1(C_57, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 2.28/1.30  tff(c_181, plain, (![B_58]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_58) | k1_relset_1(k1_xboole_0, B_58, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_177])).
% 2.28/1.30  tff(c_373, plain, (![B_86]: (v1_funct_2('#skF_4', '#skF_4', B_86) | k1_relset_1('#skF_4', B_86, '#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_216, c_216, c_216, c_181])).
% 2.28/1.30  tff(c_348, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_300])).
% 2.28/1.30  tff(c_376, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_373, c_348])).
% 2.28/1.30  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_347, c_376])).
% 2.28/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  Inference rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Ref     : 0
% 2.28/1.30  #Sup     : 75
% 2.28/1.30  #Fact    : 0
% 2.28/1.30  #Define  : 0
% 2.28/1.30  #Split   : 0
% 2.28/1.30  #Chain   : 0
% 2.28/1.30  #Close   : 0
% 2.28/1.30  
% 2.28/1.30  Ordering : KBO
% 2.28/1.30  
% 2.28/1.30  Simplification rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Subsume      : 4
% 2.28/1.30  #Demod        : 73
% 2.28/1.30  #Tautology    : 56
% 2.28/1.30  #SimpNegUnit  : 1
% 2.28/1.30  #BackRed      : 25
% 2.28/1.30  
% 2.28/1.30  #Partial instantiations: 0
% 2.28/1.30  #Strategies tried      : 1
% 2.28/1.30  
% 2.28/1.30  Timing (in seconds)
% 2.28/1.30  ----------------------
% 2.28/1.30  Preprocessing        : 0.30
% 2.28/1.30  Parsing              : 0.16
% 2.28/1.30  CNF conversion       : 0.02
% 2.28/1.30  Main loop            : 0.23
% 2.28/1.30  Inferencing          : 0.08
% 2.28/1.30  Reduction            : 0.07
% 2.28/1.30  Demodulation         : 0.05
% 2.28/1.30  BG Simplification    : 0.02
% 2.28/1.30  Subsumption          : 0.04
% 2.28/1.30  Abstraction          : 0.01
% 2.28/1.30  MUC search           : 0.00
% 2.28/1.30  Cooper               : 0.00
% 2.28/1.30  Total                : 0.56
% 2.28/1.30  Index Insertion      : 0.00
% 2.28/1.30  Index Deletion       : 0.00
% 2.28/1.30  Index Matching       : 0.00
% 2.28/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
