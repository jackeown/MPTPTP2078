%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:50 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 155 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 379 expanded)
%              Number of equality atoms :   21 ( 142 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => v1_partfun1(k3_partfun1(C,A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_16,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_27,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    ! [C_17,A_18,B_19] :
      ( k3_partfun1(C_17,A_18,B_19) = C_17
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_35])).

tff(c_41,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_38])).

tff(c_14,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_14])).

tff(c_20,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_partfun1(C_20,A_21)
      | ~ v1_funct_2(C_20,A_21,B_22)
      | ~ v1_funct_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | v1_xboole_0(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_47])).

tff(c_53,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_50])).

tff(c_54,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_53])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_57])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_69,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_63])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_83,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_partfun1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_83])).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_89,plain,(
    ! [C_27,A_28,B_29] :
      ( k3_partfun1(C_27,A_28,B_29) = C_27
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_89])).

tff(c_95,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_92])).

tff(c_81,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_96,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_81])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_20])).

tff(c_101,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_partfun1(C_30,A_31)
      | ~ v1_funct_2(C_30,A_31,B_32)
      | ~ v1_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | v1_xboole_0(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_101])).

tff(c_107,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_78,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_96,c_107])).

tff(c_110,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_117,plain,(
    ! [C_33,A_34,B_35] :
      ( k3_partfun1(C_33,A_34,B_35) = C_33
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_120,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_117])).

tff(c_123,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_120])).

tff(c_124,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_81])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.25  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.25  
% 2.18/1.25  %Foreground sorts:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Background operators:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Foreground operators:
% 2.18/1.25  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 2.18/1.25  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.18/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.25  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.18/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.25  
% 2.18/1.27  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => v1_partfun1(k3_partfun1(C, A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_funct_2)).
% 2.18/1.27  tff(f_57, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_partfun1)).
% 2.18/1.27  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.18/1.27  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 2.18/1.27  tff(f_37, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.18/1.27  tff(c_16, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.27  tff(c_27, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 2.18/1.27  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.27  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.27  tff(c_35, plain, (![C_17, A_18, B_19]: (k3_partfun1(C_17, A_18, B_19)=C_17 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_1(C_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_38, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_35])).
% 2.18/1.27  tff(c_41, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_38])).
% 2.18/1.27  tff(c_14, plain, (~v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.27  tff(c_42, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_14])).
% 2.18/1.27  tff(c_20, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.27  tff(c_47, plain, (![C_20, A_21, B_22]: (v1_partfun1(C_20, A_21) | ~v1_funct_2(C_20, A_21, B_22) | ~v1_funct_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | v1_xboole_0(B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.27  tff(c_50, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_47])).
% 2.18/1.27  tff(c_53, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_50])).
% 2.18/1.27  tff(c_54, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_53])).
% 2.18/1.27  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.18/1.27  tff(c_57, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_4])).
% 2.18/1.27  tff(c_61, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27, c_57])).
% 2.18/1.27  tff(c_62, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 2.18/1.27  tff(c_63, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16])).
% 2.18/1.27  tff(c_69, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_63])).
% 2.18/1.27  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_18])).
% 2.18/1.27  tff(c_83, plain, (![C_24, A_25, B_26]: (v1_partfun1(C_24, A_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.27  tff(c_87, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_83])).
% 2.18/1.27  tff(c_88, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_87])).
% 2.18/1.27  tff(c_89, plain, (![C_27, A_28, B_29]: (k3_partfun1(C_27, A_28, B_29)=C_27 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_92, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_89])).
% 2.18/1.27  tff(c_95, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_92])).
% 2.18/1.27  tff(c_81, plain, (~v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_14])).
% 2.18/1.27  tff(c_96, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_81])).
% 2.18/1.27  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_20])).
% 2.18/1.27  tff(c_101, plain, (![C_30, A_31, B_32]: (v1_partfun1(C_30, A_31) | ~v1_funct_2(C_30, A_31, B_32) | ~v1_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | v1_xboole_0(B_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.27  tff(c_104, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_101])).
% 2.18/1.27  tff(c_107, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_78, c_104])).
% 2.18/1.27  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_96, c_107])).
% 2.18/1.27  tff(c_110, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_87])).
% 2.18/1.27  tff(c_117, plain, (![C_33, A_34, B_35]: (k3_partfun1(C_33, A_34, B_35)=C_33 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.27  tff(c_120, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_117])).
% 2.18/1.27  tff(c_123, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_120])).
% 2.18/1.27  tff(c_124, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_81])).
% 2.18/1.27  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_124])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 21
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 3
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Subsume      : 0
% 2.18/1.27  #Demod        : 17
% 2.18/1.27  #Tautology    : 14
% 2.18/1.27  #SimpNegUnit  : 3
% 2.18/1.27  #BackRed      : 4
% 2.18/1.27  
% 2.18/1.27  #Partial instantiations: 0
% 2.18/1.27  #Strategies tried      : 1
% 2.18/1.27  
% 2.18/1.27  Timing (in seconds)
% 2.18/1.27  ----------------------
% 2.18/1.27  Preprocessing        : 0.31
% 2.18/1.27  Parsing              : 0.16
% 2.18/1.27  CNF conversion       : 0.02
% 2.18/1.27  Main loop            : 0.13
% 2.18/1.27  Inferencing          : 0.05
% 2.18/1.27  Reduction            : 0.04
% 2.18/1.27  Demodulation         : 0.03
% 2.18/1.27  BG Simplification    : 0.01
% 2.18/1.27  Subsumption          : 0.02
% 2.18/1.27  Abstraction          : 0.01
% 2.18/1.27  MUC search           : 0.00
% 2.18/1.27  Cooper               : 0.00
% 2.18/1.27  Total                : 0.47
% 2.18/1.27  Index Insertion      : 0.00
% 2.18/1.27  Index Deletion       : 0.00
% 2.18/1.27  Index Matching       : 0.00
% 2.18/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
