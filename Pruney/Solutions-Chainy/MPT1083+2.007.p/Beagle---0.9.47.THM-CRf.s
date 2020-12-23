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
% DateTime   : Thu Dec  3 10:18:17 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 139 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 426 expanded)
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

tff(f_86,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_39,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_43,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_34,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ! [A_26,B_27,C_28] :
      ( k1_relset_1(A_26,B_27,C_28) = k1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_70,plain,(
    ! [B_40,A_41,C_42] :
      ( k1_xboole_0 = B_40
      | k1_relset_1(A_41,B_40,C_42) = A_41
      | ~ v1_funct_2(C_42,A_41,B_40)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_41,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54,c_73])).

tff(c_77,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_32,B_33] :
      ( k1_relat_1(k5_relat_1(A_32,B_33)) = k1_relat_1(A_32)
      | ~ r1_tarski(k2_relat_1(A_32),k1_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [B_2,B_33] :
      ( k1_relat_1(k5_relat_1(B_2,B_33)) = k1_relat_1(B_2)
      | ~ v1_relat_1(B_33)
      | ~ v5_relat_1(B_2,k1_relat_1(B_33))
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_82,plain,(
    ! [B_2] :
      ( k1_relat_1(k5_relat_1(B_2,'#skF_2')) = k1_relat_1(B_2)
      | ~ v1_relat_1('#skF_2')
      | ~ v5_relat_1(B_2,'#skF_1')
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_66])).

tff(c_97,plain,(
    ! [B_43] :
      ( k1_relat_1(k5_relat_1(B_43,'#skF_2')) = k1_relat_1(B_43)
      | ~ v5_relat_1(B_43,'#skF_1')
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_82])).

tff(c_24,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_109,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_24])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_109])).

tff(c_119,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_118,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_20,plain,(
    ! [B_13,C_14] :
      ( k1_relset_1(k1_xboole_0,B_13,C_14) = k1_xboole_0
      | ~ v1_funct_2(C_14,k1_xboole_0,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,(
    ! [B_52,C_53] :
      ( k1_relset_1('#skF_1',B_52,C_53) = '#skF_1'
      | ~ v1_funct_2(C_53,'#skF_1',B_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_52))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_118,c_118,c_118,c_20])).

tff(c_154,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_151])).

tff(c_157,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_54,c_154])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.18  
% 2.19/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.19  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.19  
% 2.19/1.19  %Foreground sorts:
% 2.19/1.19  
% 2.19/1.19  
% 2.19/1.19  %Background operators:
% 2.19/1.19  
% 2.19/1.19  
% 2.19/1.19  %Foreground operators:
% 2.19/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.19/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.19/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.19/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.19/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.19  
% 2.19/1.20  tff(f_86, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 2.19/1.20  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.19/1.20  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.19/1.20  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.19/1.20  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.19/1.20  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.19/1.20  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.20  tff(c_28, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.20  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.20  tff(c_39, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.20  tff(c_43, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.19/1.20  tff(c_34, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.20  tff(c_50, plain, (![A_26, B_27, C_28]: (k1_relset_1(A_26, B_27, C_28)=k1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.20  tff(c_54, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_50])).
% 2.19/1.20  tff(c_70, plain, (![B_40, A_41, C_42]: (k1_xboole_0=B_40 | k1_relset_1(A_41, B_40, C_42)=A_41 | ~v1_funct_2(C_42, A_41, B_40) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_41, B_40))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.20  tff(c_73, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_70])).
% 2.19/1.20  tff(c_76, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_54, c_73])).
% 2.19/1.20  tff(c_77, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_76])).
% 2.19/1.20  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.20  tff(c_61, plain, (![A_32, B_33]: (k1_relat_1(k5_relat_1(A_32, B_33))=k1_relat_1(A_32) | ~r1_tarski(k2_relat_1(A_32), k1_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.20  tff(c_66, plain, (![B_2, B_33]: (k1_relat_1(k5_relat_1(B_2, B_33))=k1_relat_1(B_2) | ~v1_relat_1(B_33) | ~v5_relat_1(B_2, k1_relat_1(B_33)) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_61])).
% 2.19/1.20  tff(c_82, plain, (![B_2]: (k1_relat_1(k5_relat_1(B_2, '#skF_2'))=k1_relat_1(B_2) | ~v1_relat_1('#skF_2') | ~v5_relat_1(B_2, '#skF_1') | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_77, c_66])).
% 2.19/1.20  tff(c_97, plain, (![B_43]: (k1_relat_1(k5_relat_1(B_43, '#skF_2'))=k1_relat_1(B_43) | ~v5_relat_1(B_43, '#skF_1') | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_82])).
% 2.19/1.20  tff(c_24, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.19/1.20  tff(c_109, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_97, c_24])).
% 2.19/1.20  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_109])).
% 2.19/1.20  tff(c_119, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_76])).
% 2.19/1.20  tff(c_118, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_76])).
% 2.19/1.20  tff(c_20, plain, (![B_13, C_14]: (k1_relset_1(k1_xboole_0, B_13, C_14)=k1_xboole_0 | ~v1_funct_2(C_14, k1_xboole_0, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.20  tff(c_151, plain, (![B_52, C_53]: (k1_relset_1('#skF_1', B_52, C_53)='#skF_1' | ~v1_funct_2(C_53, '#skF_1', B_52) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_52))))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_118, c_118, c_118, c_20])).
% 2.19/1.20  tff(c_154, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_151])).
% 2.19/1.20  tff(c_157, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_54, c_154])).
% 2.19/1.20  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_157])).
% 2.19/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.20  
% 2.19/1.20  Inference rules
% 2.19/1.20  ----------------------
% 2.19/1.20  #Ref     : 0
% 2.19/1.20  #Sup     : 24
% 2.19/1.20  #Fact    : 0
% 2.19/1.20  #Define  : 0
% 2.19/1.20  #Split   : 1
% 2.19/1.20  #Chain   : 0
% 2.19/1.20  #Close   : 0
% 2.19/1.20  
% 2.19/1.20  Ordering : KBO
% 2.19/1.20  
% 2.19/1.20  Simplification rules
% 2.19/1.20  ----------------------
% 2.19/1.20  #Subsume      : 1
% 2.19/1.20  #Demod        : 33
% 2.19/1.20  #Tautology    : 12
% 2.19/1.20  #SimpNegUnit  : 1
% 2.19/1.20  #BackRed      : 7
% 2.19/1.20  
% 2.19/1.20  #Partial instantiations: 0
% 2.19/1.20  #Strategies tried      : 1
% 2.19/1.20  
% 2.19/1.20  Timing (in seconds)
% 2.19/1.20  ----------------------
% 2.19/1.20  Preprocessing        : 0.30
% 2.19/1.20  Parsing              : 0.16
% 2.19/1.20  CNF conversion       : 0.02
% 2.19/1.20  Main loop            : 0.16
% 2.19/1.20  Inferencing          : 0.06
% 2.19/1.20  Reduction            : 0.05
% 2.19/1.20  Demodulation         : 0.04
% 2.19/1.20  BG Simplification    : 0.01
% 2.19/1.20  Subsumption          : 0.03
% 2.19/1.20  Abstraction          : 0.01
% 2.19/1.20  MUC search           : 0.00
% 2.19/1.20  Cooper               : 0.00
% 2.19/1.20  Total                : 0.49
% 2.19/1.20  Index Insertion      : 0.00
% 2.19/1.20  Index Deletion       : 0.00
% 2.19/1.20  Index Matching       : 0.00
% 2.19/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
