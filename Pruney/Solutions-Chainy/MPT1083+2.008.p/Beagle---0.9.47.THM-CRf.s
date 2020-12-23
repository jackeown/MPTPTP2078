%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:17 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 121 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_76,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

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

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_29,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    ! [A_25,B_26,C_27] :
      ( k1_relset_1(A_25,B_26,C_27) = k1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_40])).

tff(c_55,plain,(
    ! [A_30,B_31] :
      ( k1_relset_1(A_30,A_30,B_31) = A_30
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_61,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_44,c_58])).

tff(c_6,plain,(
    ! [A_3,B_5] :
      ( k1_relat_1(k5_relat_1(A_3,B_5)) = k1_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),k1_relat_1(B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [A_3] :
      ( k1_relat_1(k5_relat_1(A_3,'#skF_2')) = k1_relat_1(A_3)
      | ~ r1_tarski(k2_relat_1(A_3),'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_6])).

tff(c_76,plain,(
    ! [A_32] :
      ( k1_relat_1(k5_relat_1(A_32,'#skF_2')) = k1_relat_1(A_32)
      | ~ r1_tarski(k2_relat_1(A_32),'#skF_1')
      | ~ v1_relat_1(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_66])).

tff(c_82,plain,(
    ! [B_33] :
      ( k1_relat_1(k5_relat_1(B_33,'#skF_2')) = k1_relat_1(B_33)
      | ~ v5_relat_1(B_33,'#skF_1')
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_14,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_91,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.13  
% 1.83/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.13  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.13  
% 1.83/1.13  %Foreground sorts:
% 1.83/1.13  
% 1.83/1.13  
% 1.83/1.13  %Background operators:
% 1.83/1.13  
% 1.83/1.13  
% 1.83/1.13  %Foreground operators:
% 1.83/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.83/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.83/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.83/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.83/1.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.83/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.13  
% 1.83/1.14  tff(f_76, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 1.83/1.14  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.83/1.14  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.83/1.14  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.83/1.14  tff(f_56, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 1.83/1.14  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 1.83/1.14  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.14  tff(c_18, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.14  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.14  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.14  tff(c_29, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.14  tff(c_33, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_29])).
% 1.83/1.14  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.14  tff(c_24, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.14  tff(c_40, plain, (![A_25, B_26, C_27]: (k1_relset_1(A_25, B_26, C_27)=k1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.14  tff(c_44, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_40])).
% 1.83/1.14  tff(c_55, plain, (![A_30, B_31]: (k1_relset_1(A_30, A_30, B_31)=A_30 | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.14  tff(c_58, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_55])).
% 1.83/1.14  tff(c_61, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_44, c_58])).
% 1.83/1.14  tff(c_6, plain, (![A_3, B_5]: (k1_relat_1(k5_relat_1(A_3, B_5))=k1_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), k1_relat_1(B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.14  tff(c_66, plain, (![A_3]: (k1_relat_1(k5_relat_1(A_3, '#skF_2'))=k1_relat_1(A_3) | ~r1_tarski(k2_relat_1(A_3), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_61, c_6])).
% 1.83/1.14  tff(c_76, plain, (![A_32]: (k1_relat_1(k5_relat_1(A_32, '#skF_2'))=k1_relat_1(A_32) | ~r1_tarski(k2_relat_1(A_32), '#skF_1') | ~v1_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_66])).
% 1.83/1.14  tff(c_82, plain, (![B_33]: (k1_relat_1(k5_relat_1(B_33, '#skF_2'))=k1_relat_1(B_33) | ~v5_relat_1(B_33, '#skF_1') | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_4, c_76])).
% 1.83/1.15  tff(c_14, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.15  tff(c_91, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_82, c_14])).
% 1.83/1.15  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_91])).
% 1.83/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  
% 1.83/1.15  Inference rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Ref     : 0
% 1.83/1.15  #Sup     : 17
% 1.83/1.15  #Fact    : 0
% 1.83/1.15  #Define  : 0
% 1.83/1.15  #Split   : 0
% 1.83/1.15  #Chain   : 0
% 1.83/1.15  #Close   : 0
% 1.83/1.15  
% 1.83/1.15  Ordering : KBO
% 1.83/1.15  
% 1.83/1.15  Simplification rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Subsume      : 0
% 1.83/1.15  #Demod        : 7
% 1.83/1.15  #Tautology    : 8
% 1.83/1.15  #SimpNegUnit  : 0
% 1.83/1.15  #BackRed      : 1
% 1.83/1.15  
% 1.83/1.15  #Partial instantiations: 0
% 1.83/1.15  #Strategies tried      : 1
% 1.83/1.15  
% 1.83/1.15  Timing (in seconds)
% 1.83/1.15  ----------------------
% 1.83/1.15  Preprocessing        : 0.28
% 1.83/1.15  Parsing              : 0.16
% 1.83/1.15  CNF conversion       : 0.02
% 1.83/1.15  Main loop            : 0.11
% 1.83/1.15  Inferencing          : 0.05
% 1.83/1.15  Reduction            : 0.03
% 1.83/1.15  Demodulation         : 0.03
% 1.83/1.15  BG Simplification    : 0.01
% 1.83/1.15  Subsumption          : 0.01
% 1.83/1.15  Abstraction          : 0.01
% 1.83/1.15  MUC search           : 0.00
% 1.83/1.15  Cooper               : 0.00
% 1.83/1.15  Total                : 0.42
% 1.83/1.15  Index Insertion      : 0.00
% 1.83/1.15  Index Deletion       : 0.00
% 1.83/1.15  Index Matching       : 0.00
% 1.83/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
