%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:13 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 143 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 386 expanded)
%              Number of equality atoms :   29 ( 175 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(c_18,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_21])).

tff(c_20,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_29,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_21])).

tff(c_8,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_29,c_8])).

tff(c_10,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_16,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_14])).

tff(c_41,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_31])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_29,c_12])).

tff(c_44,plain,(
    ! [B_12,A_13,C_14] :
      ( k1_xboole_0 = B_12
      | k8_relset_1(A_13,B_12,C_14,B_12) = A_13
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_13,B_12)))
      | ~ v1_funct_2(C_14,A_13,B_12)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_44])).

tff(c_49,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_41,c_46])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_49])).

tff(c_52,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_68,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_29])).

tff(c_53,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_62,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_28])).

tff(c_75,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_53,c_52,c_8])).

tff(c_63,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14])).

tff(c_73,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_63])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_12])).

tff(c_76,plain,(
    ! [B_15,C_16] :
      ( k8_relset_1(k1_xboole_0,B_15,C_16,B_15) = k1_xboole_0
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15)))
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_76])).

tff(c_81,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_73,c_78])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.21  
% 1.84/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.22  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.84/1.22  
% 1.84/1.22  %Foreground sorts:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Background operators:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Foreground operators:
% 1.84/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.22  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.84/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.84/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.84/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.84/1.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.84/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.84/1.22  
% 1.84/1.23  tff(f_60, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 1.84/1.23  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 1.84/1.23  tff(f_37, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 1.84/1.23  tff(c_18, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.23  tff(c_21, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.23  tff(c_28, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_21])).
% 1.84/1.23  tff(c_20, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.23  tff(c_29, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_21])).
% 1.84/1.23  tff(c_8, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.23  tff(c_42, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_29, c_8])).
% 1.84/1.23  tff(c_10, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.23  tff(c_30, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10])).
% 1.84/1.23  tff(c_16, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.23  tff(c_14, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.23  tff(c_31, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_14])).
% 1.84/1.23  tff(c_41, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_31])).
% 1.84/1.23  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.23  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_29, c_12])).
% 1.84/1.23  tff(c_44, plain, (![B_12, A_13, C_14]: (k1_xboole_0=B_12 | k8_relset_1(A_13, B_12, C_14, B_12)=A_13 | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_13, B_12))) | ~v1_funct_2(C_14, A_13, B_12) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.23  tff(c_46, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_44])).
% 1.84/1.23  tff(c_49, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_41, c_46])).
% 1.84/1.23  tff(c_51, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_49])).
% 1.84/1.23  tff(c_52, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10])).
% 1.84/1.23  tff(c_68, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_29])).
% 1.84/1.23  tff(c_53, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10])).
% 1.84/1.23  tff(c_62, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_53, c_28])).
% 1.84/1.23  tff(c_75, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_53, c_52, c_8])).
% 1.84/1.23  tff(c_63, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_14])).
% 1.84/1.23  tff(c_73, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_63])).
% 1.84/1.23  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_12])).
% 1.84/1.23  tff(c_76, plain, (![B_15, C_16]: (k8_relset_1(k1_xboole_0, B_15, C_16, B_15)=k1_xboole_0 | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))) | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.23  tff(c_78, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_76])).
% 1.84/1.23  tff(c_81, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_73, c_78])).
% 1.84/1.23  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_81])).
% 1.84/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  Inference rules
% 1.84/1.23  ----------------------
% 1.84/1.23  #Ref     : 0
% 1.84/1.23  #Sup     : 16
% 1.84/1.23  #Fact    : 0
% 1.84/1.23  #Define  : 0
% 1.84/1.23  #Split   : 1
% 1.84/1.23  #Chain   : 0
% 1.84/1.23  #Close   : 0
% 1.84/1.23  
% 1.84/1.23  Ordering : KBO
% 1.84/1.23  
% 1.84/1.23  Simplification rules
% 1.84/1.23  ----------------------
% 1.84/1.23  #Subsume      : 0
% 1.84/1.23  #Demod        : 20
% 1.84/1.23  #Tautology    : 12
% 1.84/1.23  #SimpNegUnit  : 2
% 1.84/1.23  #BackRed      : 2
% 1.84/1.23  
% 1.84/1.23  #Partial instantiations: 0
% 1.84/1.23  #Strategies tried      : 1
% 1.84/1.23  
% 1.84/1.23  Timing (in seconds)
% 1.84/1.23  ----------------------
% 1.89/1.23  Preprocessing        : 0.29
% 1.89/1.23  Parsing              : 0.15
% 1.89/1.23  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.11
% 1.89/1.23  Inferencing          : 0.03
% 1.89/1.23  Reduction            : 0.04
% 1.89/1.23  Demodulation         : 0.03
% 1.89/1.23  BG Simplification    : 0.01
% 1.89/1.23  Subsumption          : 0.01
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.43
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
