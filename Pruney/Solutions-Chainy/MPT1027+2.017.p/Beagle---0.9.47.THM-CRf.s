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
% DateTime   : Thu Dec  3 10:16:44 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 752 expanded)
%              Number of leaves         :   20 ( 248 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 (1792 expanded)
%              Number of equality atoms :   47 ( 488 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_61,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26])).

tff(c_28,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_105,plain,(
    ! [B_26,C_27,A_28] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_28,B_26)
      | k1_relset_1(A_28,B_26,C_27) != A_28
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_108])).

tff(c_118,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_117])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_130,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_128,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_118,c_8])).

tff(c_71,plain,(
    ! [B_13,A_14] :
      ( v1_xboole_0(B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_14))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_76,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_148,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_76])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_148])).

tff(c_154,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_153,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_158,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_153,c_4])).

tff(c_197,plain,(
    ! [A_37] :
      ( A_37 = '#skF_3'
      | ~ v1_xboole_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_204,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_154,c_197])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_242,plain,(
    ! [B_39,A_40] :
      ( B_39 = '#skF_3'
      | A_40 = '#skF_3'
      | k2_zfmisc_1(A_40,B_39) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_158,c_158,c_6])).

tff(c_252,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_242])).

tff(c_260,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_271,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_28])).

tff(c_227,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_30])).

tff(c_263,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_227])).

tff(c_269,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_158])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [C_9,B_8] :
      ( v1_funct_2(C_9,k1_xboole_0,B_8)
      | k1_relset_1(k1_xboole_0,B_8,C_9) != k1_xboole_0
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [C_9,B_8] :
      ( v1_funct_2(C_9,k1_xboole_0,B_8)
      | k1_relset_1(k1_xboole_0,B_8,C_9) != k1_xboole_0
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_414,plain,(
    ! [C_59,B_60] :
      ( v1_funct_2(C_59,'#skF_1',B_60)
      | k1_relset_1('#skF_1',B_60,C_59) != '#skF_1'
      | ~ m1_subset_1(C_59,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_269,c_269,c_269,c_36])).

tff(c_418,plain,(
    ! [B_61] :
      ( v1_funct_2('#skF_1','#skF_1',B_61)
      | k1_relset_1('#skF_1',B_61,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_263,c_414])).

tff(c_272,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_34])).

tff(c_426,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_418,c_272])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_426])).

tff(c_439,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_14,plain,(
    ! [A_7] :
      ( v1_funct_2(k1_xboole_0,A_7,k1_xboole_0)
      | k1_xboole_0 = A_7
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_7,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_7] :
      ( v1_funct_2(k1_xboole_0,A_7,k1_xboole_0)
      | k1_xboole_0 = A_7
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_258,plain,(
    ! [A_7] :
      ( v1_funct_2('#skF_3',A_7,'#skF_3')
      | A_7 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_158,c_158,c_158,c_158,c_158,c_38])).

tff(c_438,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_442,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_34])).

tff(c_458,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_258,c_442])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.12/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.12/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.28  
% 2.12/1.29  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.12/1.29  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.12/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.29  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.12/1.29  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.12/1.29  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.12/1.29  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.29  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.29  tff(c_26, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.29  tff(c_34, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26])).
% 2.12/1.29  tff(c_28, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.29  tff(c_105, plain, (![B_26, C_27, A_28]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_28, B_26) | k1_relset_1(A_28, B_26, C_27)!=A_28 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_26))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.29  tff(c_108, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_30, c_105])).
% 2.12/1.29  tff(c_117, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_108])).
% 2.12/1.29  tff(c_118, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_117])).
% 2.12/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.12/1.29  tff(c_130, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2])).
% 2.12/1.29  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.29  tff(c_128, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_118, c_8])).
% 2.12/1.29  tff(c_71, plain, (![B_13, A_14]: (v1_xboole_0(B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_14)) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.29  tff(c_75, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_71])).
% 2.12/1.29  tff(c_76, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_75])).
% 2.12/1.29  tff(c_148, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_76])).
% 2.12/1.29  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_148])).
% 2.12/1.29  tff(c_154, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_75])).
% 2.12/1.29  tff(c_153, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_75])).
% 2.12/1.29  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.12/1.29  tff(c_158, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_153, c_4])).
% 2.12/1.29  tff(c_197, plain, (![A_37]: (A_37='#skF_3' | ~v1_xboole_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_4])).
% 2.12/1.29  tff(c_204, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_154, c_197])).
% 2.12/1.29  tff(c_6, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.29  tff(c_242, plain, (![B_39, A_40]: (B_39='#skF_3' | A_40='#skF_3' | k2_zfmisc_1(A_40, B_39)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_158, c_158, c_6])).
% 2.12/1.29  tff(c_252, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_204, c_242])).
% 2.12/1.29  tff(c_260, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_252])).
% 2.12/1.29  tff(c_271, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_28])).
% 2.12/1.29  tff(c_227, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_30])).
% 2.12/1.29  tff(c_263, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_227])).
% 2.12/1.29  tff(c_269, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_158])).
% 2.12/1.29  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.29  tff(c_18, plain, (![C_9, B_8]: (v1_funct_2(C_9, k1_xboole_0, B_8) | k1_relset_1(k1_xboole_0, B_8, C_9)!=k1_xboole_0 | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_8))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.29  tff(c_36, plain, (![C_9, B_8]: (v1_funct_2(C_9, k1_xboole_0, B_8) | k1_relset_1(k1_xboole_0, B_8, C_9)!=k1_xboole_0 | ~m1_subset_1(C_9, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 2.12/1.29  tff(c_414, plain, (![C_59, B_60]: (v1_funct_2(C_59, '#skF_1', B_60) | k1_relset_1('#skF_1', B_60, C_59)!='#skF_1' | ~m1_subset_1(C_59, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_269, c_269, c_269, c_36])).
% 2.12/1.29  tff(c_418, plain, (![B_61]: (v1_funct_2('#skF_1', '#skF_1', B_61) | k1_relset_1('#skF_1', B_61, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_263, c_414])).
% 2.12/1.29  tff(c_272, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_34])).
% 2.12/1.29  tff(c_426, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_418, c_272])).
% 2.12/1.29  tff(c_437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_271, c_426])).
% 2.12/1.29  tff(c_439, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_252])).
% 2.12/1.29  tff(c_14, plain, (![A_7]: (v1_funct_2(k1_xboole_0, A_7, k1_xboole_0) | k1_xboole_0=A_7 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_7, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.29  tff(c_38, plain, (![A_7]: (v1_funct_2(k1_xboole_0, A_7, k1_xboole_0) | k1_xboole_0=A_7 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.12/1.29  tff(c_258, plain, (![A_7]: (v1_funct_2('#skF_3', A_7, '#skF_3') | A_7='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_158, c_158, c_158, c_158, c_158, c_38])).
% 2.12/1.29  tff(c_438, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_252])).
% 2.12/1.29  tff(c_442, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_34])).
% 2.12/1.29  tff(c_458, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_258, c_442])).
% 2.12/1.29  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_439, c_458])).
% 2.12/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  Inference rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Ref     : 0
% 2.12/1.29  #Sup     : 86
% 2.12/1.29  #Fact    : 0
% 2.12/1.29  #Define  : 0
% 2.12/1.29  #Split   : 4
% 2.12/1.29  #Chain   : 0
% 2.12/1.29  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Subsume      : 6
% 2.12/1.29  #Demod        : 119
% 2.12/1.29  #Tautology    : 72
% 2.12/1.29  #SimpNegUnit  : 2
% 2.12/1.29  #BackRed      : 38
% 2.12/1.29  
% 2.12/1.29  #Partial instantiations: 0
% 2.12/1.29  #Strategies tried      : 1
% 2.12/1.29  
% 2.12/1.29  Timing (in seconds)
% 2.12/1.29  ----------------------
% 2.12/1.29  Preprocessing        : 0.28
% 2.12/1.29  Parsing              : 0.16
% 2.12/1.29  CNF conversion       : 0.02
% 2.12/1.29  Main loop            : 0.25
% 2.12/1.29  Inferencing          : 0.09
% 2.12/1.30  Reduction            : 0.08
% 2.12/1.30  Demodulation         : 0.06
% 2.12/1.30  BG Simplification    : 0.02
% 2.12/1.30  Subsumption          : 0.05
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.57
% 2.12/1.30  Index Insertion      : 0.00
% 2.12/1.30  Index Deletion       : 0.00
% 2.12/1.30  Index Matching       : 0.00
% 2.12/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
