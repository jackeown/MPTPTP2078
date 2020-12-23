%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:42 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   58 (  92 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   89 ( 210 expanded)
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

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_80,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30])).

tff(c_112,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_partfun1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_112])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( v1_xboole_0(k2_zfmisc_1(A_1,B_2))
      | ~ v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_45,plain,(
    ! [B_23,A_24] :
      ( v1_xboole_0(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_50,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_32,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_93,plain,(
    ! [B_44,C_45,A_46] :
      ( k1_xboole_0 = B_44
      | v1_funct_2(C_45,A_46,B_44)
      | k1_relset_1(A_46,B_44,C_45) != A_46
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_96,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_99,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96])).

tff(c_100,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_99])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_107,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_107])).

tff(c_110,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_118,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_123,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_121])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_xboole_0(k1_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_8])).

tff(c_131,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_127])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_131])).

tff(c_134,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_155,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_funct_2(C_63,A_64,B_65)
      | ~ v1_partfun1(C_63,A_64)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_161,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_134,c_158])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.23  
% 1.92/1.23  %Foreground sorts:
% 1.92/1.23  
% 1.92/1.23  
% 1.92/1.23  %Background operators:
% 1.92/1.23  
% 1.92/1.23  
% 1.92/1.23  %Foreground operators:
% 1.92/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.92/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.23  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.92/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.92/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.23  
% 2.13/1.24  tff(f_93, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.13/1.24  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.13/1.24  tff(f_30, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.13/1.24  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.13/1.24  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.13/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.13/1.24  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.13/1.24  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.13/1.24  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.13/1.24  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.24  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.24  tff(c_30, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.24  tff(c_38, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30])).
% 2.13/1.24  tff(c_112, plain, (![C_47, A_48, B_49]: (v1_partfun1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.24  tff(c_116, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_112])).
% 2.13/1.24  tff(c_117, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_116])).
% 2.13/1.24  tff(c_4, plain, (![A_1, B_2]: (v1_xboole_0(k2_zfmisc_1(A_1, B_2)) | ~v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.13/1.24  tff(c_45, plain, (![B_23, A_24]: (v1_xboole_0(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.24  tff(c_49, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.13/1.24  tff(c_50, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_49])).
% 2.13/1.24  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_4, c_50])).
% 2.13/1.24  tff(c_32, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.24  tff(c_93, plain, (![B_44, C_45, A_46]: (k1_xboole_0=B_44 | v1_funct_2(C_45, A_46, B_44) | k1_relset_1(A_46, B_44, C_45)!=A_46 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_44))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.13/1.24  tff(c_96, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_34, c_93])).
% 2.13/1.24  tff(c_99, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96])).
% 2.13/1.24  tff(c_100, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_99])).
% 2.13/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.13/1.24  tff(c_107, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2])).
% 2.13/1.24  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_107])).
% 2.13/1.24  tff(c_110, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_49])).
% 2.13/1.24  tff(c_118, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.24  tff(c_121, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_118])).
% 2.13/1.24  tff(c_123, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_121])).
% 2.13/1.24  tff(c_8, plain, (![A_6]: (v1_xboole_0(k1_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.24  tff(c_127, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_8])).
% 2.13/1.24  tff(c_131, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_127])).
% 2.13/1.24  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_131])).
% 2.13/1.24  tff(c_134, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_116])).
% 2.13/1.24  tff(c_155, plain, (![C_63, A_64, B_65]: (v1_funct_2(C_63, A_64, B_65) | ~v1_partfun1(C_63, A_64) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.24  tff(c_158, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_155])).
% 2.13/1.24  tff(c_161, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_134, c_158])).
% 2.13/1.24  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_161])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.13/1.24  #Sup     : 22
% 2.13/1.24  #Fact    : 0
% 2.13/1.24  #Define  : 0
% 2.13/1.24  #Split   : 3
% 2.13/1.24  #Chain   : 0
% 2.13/1.24  #Close   : 0
% 2.13/1.24  
% 2.13/1.24  Ordering : KBO
% 2.13/1.24  
% 2.13/1.24  Simplification rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Subsume      : 1
% 2.13/1.24  #Demod        : 33
% 2.13/1.24  #Tautology    : 9
% 2.13/1.24  #SimpNegUnit  : 6
% 2.13/1.24  #BackRed      : 7
% 2.13/1.24  
% 2.13/1.24  #Partial instantiations: 0
% 2.13/1.24  #Strategies tried      : 1
% 2.13/1.24  
% 2.13/1.24  Timing (in seconds)
% 2.13/1.24  ----------------------
% 2.13/1.24  Preprocessing        : 0.31
% 2.13/1.24  Parsing              : 0.16
% 2.13/1.24  CNF conversion       : 0.02
% 2.13/1.24  Main loop            : 0.16
% 2.13/1.24  Inferencing          : 0.05
% 2.13/1.24  Reduction            : 0.05
% 2.13/1.24  Demodulation         : 0.04
% 2.13/1.24  BG Simplification    : 0.01
% 2.13/1.24  Subsumption          : 0.03
% 2.13/1.24  Abstraction          : 0.01
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.50
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
