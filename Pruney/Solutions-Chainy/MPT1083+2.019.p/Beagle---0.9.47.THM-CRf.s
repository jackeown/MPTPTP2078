%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 142 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 432 expanded)
%              Number of equality atoms :   29 ( 140 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_45])).

tff(c_36,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_55])).

tff(c_81,plain,(
    ! [B_46,A_47,C_48] :
      ( k1_xboole_0 = B_46
      | k1_relset_1(A_47,B_46,C_48) = A_47
      | ~ v1_funct_2(C_48,A_47,B_46)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_87,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_84])).

tff(c_88,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1(k5_relat_1(A_39,B_40)) = k1_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(A_39),k1_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [B_5,B_40] :
      ( k1_relat_1(k5_relat_1(B_5,B_40)) = k1_relat_1(B_5)
      | ~ v1_relat_1(B_40)
      | ~ v5_relat_1(B_5,k1_relat_1(B_40))
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_93,plain,(
    ! [B_5] :
      ( k1_relat_1(k5_relat_1(B_5,'#skF_2')) = k1_relat_1(B_5)
      | ~ v1_relat_1('#skF_2')
      | ~ v5_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_73])).

tff(c_108,plain,(
    ! [B_49] :
      ( k1_relat_1(k5_relat_1(B_49,'#skF_2')) = k1_relat_1(B_49)
      | ~ v5_relat_1(B_49,'#skF_1')
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_93])).

tff(c_26,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_120,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_26])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_120])).

tff(c_130,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_129,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_22,plain,(
    ! [B_15,C_16] :
      ( k1_relset_1(k1_xboole_0,B_15,C_16) = k1_xboole_0
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_150,plain,(
    ! [B_53,C_54] :
      ( k1_relset_1('#skF_1',B_53,C_54) = '#skF_1'
      | ~ v1_funct_2(C_54,'#skF_1',B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_53))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_129,c_129,c_129,c_22])).

tff(c_153,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_150])).

tff(c_156,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.25  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.25  
% 2.18/1.25  %Foreground sorts:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Background operators:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Foreground operators:
% 2.18/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.18/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.25  
% 2.18/1.26  tff(f_91, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 2.18/1.26  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.26  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.26  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.18/1.26  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.18/1.26  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.18/1.26  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.18/1.26  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.26  tff(c_30, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.26  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.26  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.26  tff(c_42, plain, (![B_23, A_24]: (v1_relat_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.26  tff(c_45, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.18/1.26  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_45])).
% 2.18/1.26  tff(c_36, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.26  tff(c_55, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.26  tff(c_59, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_55])).
% 2.18/1.26  tff(c_81, plain, (![B_46, A_47, C_48]: (k1_xboole_0=B_46 | k1_relset_1(A_47, B_46, C_48)=A_47 | ~v1_funct_2(C_48, A_47, B_46) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.26  tff(c_84, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_81])).
% 2.18/1.26  tff(c_87, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_84])).
% 2.18/1.26  tff(c_88, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_87])).
% 2.18/1.26  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.26  tff(c_68, plain, (![A_39, B_40]: (k1_relat_1(k5_relat_1(A_39, B_40))=k1_relat_1(A_39) | ~r1_tarski(k2_relat_1(A_39), k1_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.26  tff(c_73, plain, (![B_5, B_40]: (k1_relat_1(k5_relat_1(B_5, B_40))=k1_relat_1(B_5) | ~v1_relat_1(B_40) | ~v5_relat_1(B_5, k1_relat_1(B_40)) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_68])).
% 2.18/1.26  tff(c_93, plain, (![B_5]: (k1_relat_1(k5_relat_1(B_5, '#skF_2'))=k1_relat_1(B_5) | ~v1_relat_1('#skF_2') | ~v5_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_88, c_73])).
% 2.18/1.26  tff(c_108, plain, (![B_49]: (k1_relat_1(k5_relat_1(B_49, '#skF_2'))=k1_relat_1(B_49) | ~v5_relat_1(B_49, '#skF_1') | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_93])).
% 2.18/1.26  tff(c_26, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.26  tff(c_120, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_108, c_26])).
% 2.18/1.26  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_120])).
% 2.18/1.26  tff(c_130, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_87])).
% 2.18/1.26  tff(c_129, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_87])).
% 2.18/1.26  tff(c_22, plain, (![B_15, C_16]: (k1_relset_1(k1_xboole_0, B_15, C_16)=k1_xboole_0 | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.26  tff(c_150, plain, (![B_53, C_54]: (k1_relset_1('#skF_1', B_53, C_54)='#skF_1' | ~v1_funct_2(C_54, '#skF_1', B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_53))))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_129, c_129, c_129, c_22])).
% 2.18/1.26  tff(c_153, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_150])).
% 2.18/1.26  tff(c_156, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_153])).
% 2.18/1.26  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_156])).
% 2.18/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.26  
% 2.18/1.26  Inference rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Ref     : 0
% 2.18/1.26  #Sup     : 23
% 2.18/1.26  #Fact    : 0
% 2.18/1.26  #Define  : 0
% 2.18/1.26  #Split   : 1
% 2.18/1.26  #Chain   : 0
% 2.18/1.26  #Close   : 0
% 2.18/1.26  
% 2.18/1.26  Ordering : KBO
% 2.18/1.26  
% 2.18/1.26  Simplification rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Subsume      : 0
% 2.18/1.26  #Demod        : 32
% 2.18/1.26  #Tautology    : 12
% 2.18/1.26  #SimpNegUnit  : 1
% 2.18/1.26  #BackRed      : 7
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.32
% 2.18/1.26  Parsing              : 0.17
% 2.18/1.27  CNF conversion       : 0.02
% 2.18/1.27  Main loop            : 0.17
% 2.18/1.27  Inferencing          : 0.06
% 2.18/1.27  Reduction            : 0.05
% 2.18/1.27  Demodulation         : 0.04
% 2.18/1.27  BG Simplification    : 0.01
% 2.18/1.27  Subsumption          : 0.03
% 2.18/1.27  Abstraction          : 0.01
% 2.18/1.27  MUC search           : 0.00
% 2.18/1.27  Cooper               : 0.00
% 2.18/1.27  Total                : 0.53
% 2.18/1.27  Index Insertion      : 0.00
% 2.18/1.27  Index Deletion       : 0.00
% 2.18/1.27  Index Matching       : 0.00
% 2.18/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
