%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   55 (  89 expanded)
%              Number of leaves         :   24 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 205 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_76,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28])).

tff(c_105,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_partfun1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_110,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_42,plain,(
    ! [C_20,B_21,A_22] :
      ( v1_xboole_0(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(B_21,A_22)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_42])).

tff(c_47,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_30,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_86,plain,(
    ! [B_42,C_43,A_44] :
      ( k1_xboole_0 = B_42
      | v1_funct_2(C_43,A_44,B_42)
      | k1_relset_1(A_44,B_42,C_43) != A_44
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_89,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_86])).

tff(c_92,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_89])).

tff(c_93,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_92])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_100,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_100])).

tff(c_103,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_112,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_117,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_115])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_relat_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_121,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_4])).

tff(c_125,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_121])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_125])).

tff(c_128,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_148,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_funct_2(C_60,A_61,B_62)
      | ~ v1_partfun1(C_60,A_61)
      | ~ v1_funct_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_151,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_148])).

tff(c_154,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_128,c_151])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:42:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.98/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.21  
% 1.98/1.22  tff(f_89, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 1.98/1.22  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 1.98/1.22  tff(f_37, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 1.98/1.22  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.98/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.22  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.98/1.22  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 1.98/1.22  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 1.98/1.22  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.98/1.22  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.98/1.22  tff(c_28, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.98/1.22  tff(c_36, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28])).
% 1.98/1.22  tff(c_105, plain, (![C_45, A_46, B_47]: (v1_partfun1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.22  tff(c_109, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_105])).
% 1.98/1.22  tff(c_110, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_109])).
% 1.98/1.22  tff(c_42, plain, (![C_20, B_21, A_22]: (v1_xboole_0(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(B_21, A_22))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.22  tff(c_46, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_42])).
% 1.98/1.22  tff(c_47, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 1.98/1.22  tff(c_30, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.98/1.22  tff(c_86, plain, (![B_42, C_43, A_44]: (k1_xboole_0=B_42 | v1_funct_2(C_43, A_44, B_42) | k1_relset_1(A_44, B_42, C_43)!=A_44 | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_42))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.98/1.22  tff(c_89, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_32, c_86])).
% 1.98/1.22  tff(c_92, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_89])).
% 1.98/1.22  tff(c_93, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_92])).
% 1.98/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.98/1.22  tff(c_100, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_2])).
% 1.98/1.22  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_100])).
% 1.98/1.22  tff(c_103, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 1.98/1.22  tff(c_112, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.22  tff(c_115, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_112])).
% 1.98/1.22  tff(c_117, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_115])).
% 1.98/1.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(k1_relat_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.98/1.22  tff(c_121, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_117, c_4])).
% 1.98/1.22  tff(c_125, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_121])).
% 1.98/1.22  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_125])).
% 1.98/1.22  tff(c_128, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_109])).
% 1.98/1.22  tff(c_148, plain, (![C_60, A_61, B_62]: (v1_funct_2(C_60, A_61, B_62) | ~v1_partfun1(C_60, A_61) | ~v1_funct_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.22  tff(c_151, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_148])).
% 1.98/1.22  tff(c_154, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_128, c_151])).
% 1.98/1.22  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_154])).
% 1.98/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  Inference rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Ref     : 0
% 1.98/1.22  #Sup     : 21
% 1.98/1.22  #Fact    : 0
% 1.98/1.22  #Define  : 0
% 1.98/1.22  #Split   : 3
% 1.98/1.22  #Chain   : 0
% 1.98/1.22  #Close   : 0
% 1.98/1.22  
% 1.98/1.22  Ordering : KBO
% 1.98/1.22  
% 1.98/1.22  Simplification rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Subsume      : 1
% 1.98/1.22  #Demod        : 33
% 1.98/1.22  #Tautology    : 9
% 1.98/1.22  #SimpNegUnit  : 6
% 1.98/1.22  #BackRed      : 7
% 1.98/1.22  
% 1.98/1.22  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 1.98/1.22  Preprocessing        : 0.30
% 1.98/1.22  Parsing              : 0.16
% 1.98/1.22  CNF conversion       : 0.02
% 1.98/1.22  Main loop            : 0.15
% 1.98/1.22  Inferencing          : 0.05
% 1.98/1.22  Reduction            : 0.05
% 1.98/1.22  Demodulation         : 0.04
% 1.98/1.22  BG Simplification    : 0.01
% 1.98/1.22  Subsumption          : 0.02
% 1.98/1.22  Abstraction          : 0.01
% 1.98/1.22  MUC search           : 0.00
% 1.98/1.22  Cooper               : 0.00
% 1.98/1.22  Total                : 0.49
% 1.98/1.22  Index Insertion      : 0.00
% 1.98/1.22  Index Deletion       : 0.00
% 1.98/1.22  Index Matching       : 0.00
% 1.98/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
