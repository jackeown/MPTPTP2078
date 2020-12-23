%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   56 (1150 expanded)
%              Number of leaves         :   19 ( 379 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 (2777 expanded)
%              Number of equality atoms :   29 ( 603 expanded)
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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_55,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39,plain,(
    ! [C_10,B_11,A_12] :
      ( v1_xboole_0(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(B_11,A_12)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_39])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20])).

tff(c_22,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_49,plain,(
    ! [B_20,C_21,A_22] :
      ( k1_xboole_0 = B_20
      | v1_funct_2(C_21,A_22,B_20)
      | k1_relset_1(A_22,B_20,C_21) != A_22
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_55,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_52])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_55])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_63,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_63])).

tff(c_66,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_67,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_85,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76])).

tff(c_89,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_28])).

tff(c_87,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_24])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_funct_2(k1_xboole_0,A_6,k1_xboole_0)
      | k1_xboole_0 = A_6
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_6,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_3',A_25,'#skF_3')
      | A_25 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_25,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_72,c_72,c_8])).

tff(c_114,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_87,c_111])).

tff(c_117,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_114])).

tff(c_128,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_89])).

tff(c_88,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_22])).

tff(c_127,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_88])).

tff(c_126,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_87])).

tff(c_131,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_72])).

tff(c_12,plain,(
    ! [C_8,B_7] :
      ( v1_funct_2(C_8,k1_xboole_0,B_7)
      | k1_relset_1(k1_xboole_0,B_7,C_8) != k1_xboole_0
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_163,plain,(
    ! [C_29,B_30] :
      ( v1_funct_2(C_29,'#skF_1',B_30)
      | k1_relset_1('#skF_1',B_30,C_29) != '#skF_1'
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_30))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_131,c_131,c_12])).

tff(c_166,plain,
    ( v1_funct_2('#skF_1','#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_126,c_163])).

tff(c_169,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.25  
% 1.97/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.25  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.25  
% 1.97/1.25  %Foreground sorts:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Background operators:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Foreground operators:
% 1.97/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.97/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.97/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.25  
% 1.97/1.26  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 1.97/1.26  tff(f_37, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.97/1.26  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.97/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.97/1.26  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.97/1.26  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.26  tff(c_39, plain, (![C_10, B_11, A_12]: (v1_xboole_0(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(B_11, A_12))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.26  tff(c_43, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_39])).
% 1.97/1.26  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_43])).
% 1.97/1.26  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.26  tff(c_20, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.26  tff(c_28, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20])).
% 1.97/1.26  tff(c_22, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.26  tff(c_49, plain, (![B_20, C_21, A_22]: (k1_xboole_0=B_20 | v1_funct_2(C_21, A_22, B_20) | k1_relset_1(A_22, B_20, C_21)!=A_22 | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_20))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.26  tff(c_52, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_24, c_49])).
% 1.97/1.26  tff(c_55, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_52])).
% 1.97/1.26  tff(c_56, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_28, c_55])).
% 1.97/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.97/1.26  tff(c_63, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2])).
% 1.97/1.26  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_63])).
% 1.97/1.26  tff(c_66, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_43])).
% 1.97/1.26  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.97/1.26  tff(c_72, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_66, c_4])).
% 1.97/1.26  tff(c_67, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_43])).
% 1.97/1.26  tff(c_76, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_67, c_4])).
% 1.97/1.26  tff(c_85, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76])).
% 1.97/1.26  tff(c_89, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_28])).
% 1.97/1.26  tff(c_87, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_24])).
% 1.97/1.26  tff(c_8, plain, (![A_6]: (v1_funct_2(k1_xboole_0, A_6, k1_xboole_0) | k1_xboole_0=A_6 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_6, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.26  tff(c_111, plain, (![A_25]: (v1_funct_2('#skF_3', A_25, '#skF_3') | A_25='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_25, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_72, c_72, c_8])).
% 1.97/1.26  tff(c_114, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_87, c_111])).
% 1.97/1.26  tff(c_117, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_89, c_114])).
% 1.97/1.26  tff(c_128, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_89])).
% 1.97/1.26  tff(c_88, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_22])).
% 1.97/1.26  tff(c_127, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_88])).
% 1.97/1.26  tff(c_126, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_87])).
% 1.97/1.26  tff(c_131, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_72])).
% 1.97/1.26  tff(c_12, plain, (![C_8, B_7]: (v1_funct_2(C_8, k1_xboole_0, B_7) | k1_relset_1(k1_xboole_0, B_7, C_8)!=k1_xboole_0 | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_7))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.26  tff(c_163, plain, (![C_29, B_30]: (v1_funct_2(C_29, '#skF_1', B_30) | k1_relset_1('#skF_1', B_30, C_29)!='#skF_1' | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_30))))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_131, c_131, c_12])).
% 1.97/1.26  tff(c_166, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_126, c_163])).
% 1.97/1.26  tff(c_169, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_166])).
% 1.97/1.26  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_169])).
% 1.97/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  
% 1.97/1.26  Inference rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Ref     : 0
% 1.97/1.26  #Sup     : 28
% 1.97/1.26  #Fact    : 0
% 1.97/1.26  #Define  : 0
% 1.97/1.26  #Split   : 1
% 1.97/1.26  #Chain   : 0
% 1.97/1.26  #Close   : 0
% 1.97/1.26  
% 1.97/1.26  Ordering : KBO
% 1.97/1.26  
% 1.97/1.26  Simplification rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Subsume      : 1
% 1.97/1.26  #Demod        : 70
% 1.97/1.26  #Tautology    : 23
% 1.97/1.26  #SimpNegUnit  : 4
% 1.97/1.26  #BackRed      : 24
% 1.97/1.26  
% 1.97/1.26  #Partial instantiations: 0
% 1.97/1.26  #Strategies tried      : 1
% 1.97/1.26  
% 1.97/1.26  Timing (in seconds)
% 1.97/1.26  ----------------------
% 1.97/1.27  Preprocessing        : 0.29
% 1.97/1.27  Parsing              : 0.16
% 1.97/1.27  CNF conversion       : 0.02
% 1.97/1.27  Main loop            : 0.16
% 1.97/1.27  Inferencing          : 0.05
% 1.97/1.27  Reduction            : 0.05
% 1.97/1.27  Demodulation         : 0.04
% 1.97/1.27  BG Simplification    : 0.01
% 1.97/1.27  Subsumption          : 0.03
% 1.97/1.27  Abstraction          : 0.01
% 1.97/1.27  MUC search           : 0.00
% 1.97/1.27  Cooper               : 0.00
% 1.97/1.27  Total                : 0.48
% 1.97/1.27  Index Insertion      : 0.00
% 1.97/1.27  Index Deletion       : 0.00
% 1.97/1.27  Index Matching       : 0.00
% 1.97/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
