%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:50 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   54 (  95 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 211 expanded)
%              Number of equality atoms :   19 (  75 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => v1_partfun1(k3_partfun1(C,A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_16,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_23,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [C_20,A_21,B_22] :
      ( k3_partfun1(C_20,A_21,B_22) = C_20
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_40])).

tff(c_46,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_43])).

tff(c_14,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_20,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_partfun1(C_23,A_24)
      | ~ v1_funct_2(C_23,A_24,B_25)
      | ~ v1_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | v1_xboole_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_55,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_58,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_55])).

tff(c_59,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_58])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [B_14,A_15] :
      ( ~ v1_xboole_0(B_14)
      | B_14 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_27,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_59,c_27])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23,c_62])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_71,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_76,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_18])).

tff(c_94,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_partfun1(C_29,A_30)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_93,c_94])).

tff(c_100,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_97])).

tff(c_101,plain,(
    ! [C_32,A_33,B_34] :
      ( k3_partfun1(C_32,A_33,B_34) = C_32
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_101])).

tff(c_107,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_104])).

tff(c_82,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_108,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_82])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.37  
% 1.89/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.37  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.37  
% 1.89/1.37  %Foreground sorts:
% 1.89/1.37  
% 1.89/1.37  
% 1.89/1.37  %Background operators:
% 1.89/1.37  
% 1.89/1.37  
% 1.89/1.37  %Foreground operators:
% 1.89/1.37  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.89/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.89/1.37  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.37  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.89/1.37  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.37  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.37  
% 2.02/1.39  tff(f_74, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => v1_partfun1(k3_partfun1(C, A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_funct_2)).
% 2.02/1.39  tff(f_61, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_partfun1)).
% 2.02/1.39  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.02/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.02/1.39  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.02/1.39  tff(f_41, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.02/1.39  tff(c_16, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.39  tff(c_23, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 2.02/1.39  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.39  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.39  tff(c_40, plain, (![C_20, A_21, B_22]: (k3_partfun1(C_20, A_21, B_22)=C_20 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.39  tff(c_43, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_40])).
% 2.02/1.39  tff(c_46, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_43])).
% 2.02/1.39  tff(c_14, plain, (~v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.39  tff(c_47, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 2.02/1.39  tff(c_20, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.39  tff(c_52, plain, (![C_23, A_24, B_25]: (v1_partfun1(C_23, A_24) | ~v1_funct_2(C_23, A_24, B_25) | ~v1_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | v1_xboole_0(B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.39  tff(c_55, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_52])).
% 2.02/1.39  tff(c_58, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_55])).
% 2.02/1.39  tff(c_59, plain, (v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_47, c_58])).
% 2.02/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.02/1.39  tff(c_24, plain, (![B_14, A_15]: (~v1_xboole_0(B_14) | B_14=A_15 | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.39  tff(c_27, plain, (![A_15]: (k1_xboole_0=A_15 | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_2, c_24])).
% 2.02/1.39  tff(c_62, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_59, c_27])).
% 2.02/1.39  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23, c_62])).
% 2.02/1.39  tff(c_69, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16])).
% 2.02/1.39  tff(c_71, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2])).
% 2.02/1.39  tff(c_70, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16])).
% 2.02/1.39  tff(c_76, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70])).
% 2.02/1.39  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_18])).
% 2.02/1.39  tff(c_94, plain, (![C_29, A_30, B_31]: (v1_partfun1(C_29, A_30) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.39  tff(c_97, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_93, c_94])).
% 2.02/1.39  tff(c_100, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_97])).
% 2.02/1.39  tff(c_101, plain, (![C_32, A_33, B_34]: (k3_partfun1(C_32, A_33, B_34)=C_32 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.39  tff(c_104, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_101])).
% 2.02/1.39  tff(c_107, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_104])).
% 2.02/1.39  tff(c_82, plain, (~v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14])).
% 2.02/1.39  tff(c_108, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_82])).
% 2.02/1.39  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_108])).
% 2.02/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.39  
% 2.02/1.39  Inference rules
% 2.02/1.39  ----------------------
% 2.02/1.39  #Ref     : 0
% 2.02/1.39  #Sup     : 17
% 2.02/1.39  #Fact    : 0
% 2.02/1.39  #Define  : 0
% 2.02/1.39  #Split   : 2
% 2.02/1.39  #Chain   : 0
% 2.02/1.39  #Close   : 0
% 2.02/1.39  
% 2.02/1.39  Ordering : KBO
% 2.02/1.39  
% 2.02/1.39  Simplification rules
% 2.02/1.39  ----------------------
% 2.02/1.39  #Subsume      : 0
% 2.02/1.39  #Demod        : 13
% 2.02/1.39  #Tautology    : 9
% 2.02/1.39  #SimpNegUnit  : 2
% 2.02/1.39  #BackRed      : 3
% 2.02/1.39  
% 2.02/1.39  #Partial instantiations: 0
% 2.02/1.39  #Strategies tried      : 1
% 2.02/1.39  
% 2.02/1.39  Timing (in seconds)
% 2.02/1.39  ----------------------
% 2.02/1.39  Preprocessing        : 0.40
% 2.02/1.39  Parsing              : 0.24
% 2.02/1.39  CNF conversion       : 0.02
% 2.02/1.39  Main loop            : 0.12
% 2.02/1.39  Inferencing          : 0.04
% 2.02/1.39  Reduction            : 0.03
% 2.02/1.39  Demodulation         : 0.03
% 2.02/1.39  BG Simplification    : 0.01
% 2.02/1.39  Subsumption          : 0.02
% 2.02/1.39  Abstraction          : 0.01
% 2.02/1.39  MUC search           : 0.00
% 2.02/1.39  Cooper               : 0.00
% 2.02/1.39  Total                : 0.54
% 2.02/1.39  Index Insertion      : 0.00
% 2.02/1.39  Index Deletion       : 0.00
% 2.02/1.39  Index Matching       : 0.00
% 2.02/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
