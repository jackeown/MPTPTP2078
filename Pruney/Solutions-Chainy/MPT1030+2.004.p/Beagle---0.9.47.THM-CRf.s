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
% DateTime   : Thu Dec  3 10:16:50 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 103 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 261 expanded)
%              Number of equality atoms :   20 ( 103 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => v1_partfun1(k3_partfun1(C,A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [C_7,A_8,B_9] :
      ( k3_partfun1(C_7,A_8,B_9) = C_7
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_18])).

tff(c_24,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_21])).

tff(c_8,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_25,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_10,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_17,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_14,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_31,plain,(
    ! [B_12,C_13,A_14] :
      ( k1_xboole_0 = B_12
      | v1_partfun1(C_13,A_14)
      | ~ v1_funct_2(C_13,A_14,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_14,B_12)))
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_31])).

tff(c_37,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_34])).

tff(c_39,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_17,c_37])).

tff(c_40,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_46,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_41])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_54,plain,(
    ! [C_15,A_16,B_17] :
      ( k3_partfun1(C_15,A_16,B_17) = C_15
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_54])).

tff(c_60,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_57])).

tff(c_52,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_61,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_47,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_2,plain,(
    ! [C_3,B_2] :
      ( v1_partfun1(C_3,k1_xboole_0)
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [C_18,B_19] :
      ( v1_partfun1(C_18,'#skF_1')
      | ~ v1_funct_2(C_18,'#skF_1',B_19)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_19)))
      | ~ v1_funct_1(C_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_40,c_2])).

tff(c_70,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_67])).

tff(c_73,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_47,c_70])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.11  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.65/1.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.65/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.11  
% 1.65/1.12  tff(f_61, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => v1_partfun1(k3_partfun1(C, A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_funct_2)).
% 1.65/1.12  tff(f_48, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 1.65/1.12  tff(f_42, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 1.65/1.12  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.65/1.12  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.65/1.12  tff(c_18, plain, (![C_7, A_8, B_9]: (k3_partfun1(C_7, A_8, B_9)=C_7 | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.65/1.12  tff(c_21, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_18])).
% 1.65/1.12  tff(c_24, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_21])).
% 1.65/1.12  tff(c_8, plain, (~v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.65/1.12  tff(c_25, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 1.65/1.12  tff(c_10, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.65/1.12  tff(c_17, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_10])).
% 1.65/1.12  tff(c_14, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.65/1.12  tff(c_31, plain, (![B_12, C_13, A_14]: (k1_xboole_0=B_12 | v1_partfun1(C_13, A_14) | ~v1_funct_2(C_13, A_14, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_14, B_12))) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.65/1.12  tff(c_34, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_31])).
% 1.65/1.12  tff(c_37, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_34])).
% 1.65/1.12  tff(c_39, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_17, c_37])).
% 1.65/1.12  tff(c_40, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_10])).
% 1.65/1.12  tff(c_41, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_10])).
% 1.65/1.12  tff(c_46, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_41])).
% 1.65/1.12  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 1.65/1.12  tff(c_54, plain, (![C_15, A_16, B_17]: (k3_partfun1(C_15, A_16, B_17)=C_15 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.65/1.12  tff(c_57, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_53, c_54])).
% 1.65/1.12  tff(c_60, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_57])).
% 1.65/1.12  tff(c_52, plain, (~v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 1.65/1.12  tff(c_61, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 1.65/1.12  tff(c_47, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 1.65/1.12  tff(c_2, plain, (![C_3, B_2]: (v1_partfun1(C_3, k1_xboole_0) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.65/1.12  tff(c_67, plain, (![C_18, B_19]: (v1_partfun1(C_18, '#skF_1') | ~v1_funct_2(C_18, '#skF_1', B_19) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_19))) | ~v1_funct_1(C_18))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_40, c_2])).
% 1.65/1.12  tff(c_70, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_53, c_67])).
% 1.65/1.12  tff(c_73, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_47, c_70])).
% 1.65/1.12  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_73])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 12
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 1
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 0
% 1.65/1.12  #Demod        : 15
% 1.65/1.12  #Tautology    : 8
% 1.65/1.12  #SimpNegUnit  : 2
% 1.65/1.12  #BackRed      : 3
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.13  Preprocessing        : 0.28
% 1.65/1.13  Parsing              : 0.15
% 1.65/1.13  CNF conversion       : 0.02
% 1.65/1.13  Main loop            : 0.09
% 1.65/1.13  Inferencing          : 0.03
% 1.65/1.13  Reduction            : 0.03
% 1.65/1.13  Demodulation         : 0.02
% 1.65/1.13  BG Simplification    : 0.01
% 1.65/1.13  Subsumption          : 0.01
% 1.65/1.13  Abstraction          : 0.00
% 1.65/1.13  MUC search           : 0.00
% 1.65/1.13  Cooper               : 0.00
% 1.65/1.13  Total                : 0.39
% 1.65/1.13  Index Insertion      : 0.00
% 1.65/1.13  Index Deletion       : 0.00
% 1.65/1.13  Index Matching       : 0.00
% 1.65/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
