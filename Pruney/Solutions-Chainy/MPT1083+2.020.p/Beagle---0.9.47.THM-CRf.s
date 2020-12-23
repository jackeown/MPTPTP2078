%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:19 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 128 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_81,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_45,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_61,plain,(
    ! [A_35,B_36] :
      ( k1_relset_1(A_35,A_35,B_36) = A_35
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_zfmisc_1(A_35,A_35)))
      | ~ v1_funct_2(B_36,A_35,A_35)
      | ~ v1_funct_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_67,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_49,c_64])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k5_relat_1(A_31,B_32)) = k1_relat_1(A_31)
      | ~ r1_tarski(k2_relat_1(A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [B_5,B_32] :
      ( k1_relat_1(k5_relat_1(B_5,B_32)) = k1_relat_1(B_5)
      | ~ v1_relat_1(B_32)
      | ~ v5_relat_1(B_5,k1_relat_1(B_32))
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_72,plain,(
    ! [B_5] :
      ( k1_relat_1(k5_relat_1(B_5,'#skF_2')) = k1_relat_1(B_5)
      | ~ v1_relat_1('#skF_2')
      | ~ v5_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_59])).

tff(c_87,plain,(
    ! [B_37] :
      ( k1_relat_1(k5_relat_1(B_37,'#skF_2')) = k1_relat_1(B_37)
      | ~ v5_relat_1(B_37,'#skF_1')
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72])).

tff(c_16,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_99,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_16])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.26  
% 1.90/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.26  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.26  
% 1.90/1.26  %Foreground sorts:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Background operators:
% 1.90/1.26  
% 1.90/1.26  
% 1.90/1.26  %Foreground operators:
% 1.90/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.90/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.90/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.90/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.90/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.26  
% 1.90/1.27  tff(f_81, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 1.90/1.27  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.90/1.27  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.90/1.27  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.90/1.27  tff(f_61, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 1.90/1.27  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.90/1.27  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 1.90/1.27  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.90/1.27  tff(c_20, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.90/1.27  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.27  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.90/1.27  tff(c_32, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.27  tff(c_35, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_32])).
% 1.90/1.27  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_35])).
% 1.90/1.27  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.90/1.27  tff(c_26, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.90/1.27  tff(c_45, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.27  tff(c_49, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_45])).
% 1.90/1.27  tff(c_61, plain, (![A_35, B_36]: (k1_relset_1(A_35, A_35, B_36)=A_35 | ~m1_subset_1(B_36, k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))) | ~v1_funct_2(B_36, A_35, A_35) | ~v1_funct_1(B_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.27  tff(c_64, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_61])).
% 1.90/1.27  tff(c_67, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_49, c_64])).
% 1.90/1.27  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.27  tff(c_54, plain, (![A_31, B_32]: (k1_relat_1(k5_relat_1(A_31, B_32))=k1_relat_1(A_31) | ~r1_tarski(k2_relat_1(A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.90/1.27  tff(c_59, plain, (![B_5, B_32]: (k1_relat_1(k5_relat_1(B_5, B_32))=k1_relat_1(B_5) | ~v1_relat_1(B_32) | ~v5_relat_1(B_5, k1_relat_1(B_32)) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_54])).
% 1.90/1.27  tff(c_72, plain, (![B_5]: (k1_relat_1(k5_relat_1(B_5, '#skF_2'))=k1_relat_1(B_5) | ~v1_relat_1('#skF_2') | ~v5_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_67, c_59])).
% 1.90/1.27  tff(c_87, plain, (![B_37]: (k1_relat_1(k5_relat_1(B_37, '#skF_2'))=k1_relat_1(B_37) | ~v5_relat_1(B_37, '#skF_1') | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_72])).
% 1.90/1.27  tff(c_16, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.90/1.27  tff(c_99, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_87, c_16])).
% 1.90/1.27  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_99])).
% 1.90/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.27  
% 1.90/1.27  Inference rules
% 1.90/1.27  ----------------------
% 1.90/1.27  #Ref     : 0
% 1.90/1.27  #Sup     : 18
% 2.03/1.27  #Fact    : 0
% 2.03/1.27  #Define  : 0
% 2.03/1.27  #Split   : 0
% 2.03/1.27  #Chain   : 0
% 2.03/1.27  #Close   : 0
% 2.03/1.27  
% 2.03/1.27  Ordering : KBO
% 2.03/1.27  
% 2.03/1.27  Simplification rules
% 2.03/1.27  ----------------------
% 2.03/1.27  #Subsume      : 0
% 2.03/1.27  #Demod        : 9
% 2.03/1.27  #Tautology    : 8
% 2.03/1.27  #SimpNegUnit  : 0
% 2.03/1.27  #BackRed      : 1
% 2.03/1.27  
% 2.03/1.27  #Partial instantiations: 0
% 2.03/1.27  #Strategies tried      : 1
% 2.03/1.27  
% 2.03/1.27  Timing (in seconds)
% 2.03/1.27  ----------------------
% 2.03/1.28  Preprocessing        : 0.31
% 2.03/1.28  Parsing              : 0.17
% 2.03/1.28  CNF conversion       : 0.02
% 2.03/1.28  Main loop            : 0.13
% 2.03/1.28  Inferencing          : 0.05
% 2.03/1.28  Reduction            : 0.04
% 2.03/1.28  Demodulation         : 0.03
% 2.03/1.28  BG Simplification    : 0.01
% 2.03/1.28  Subsumption          : 0.02
% 2.03/1.28  Abstraction          : 0.01
% 2.03/1.28  MUC search           : 0.00
% 2.03/1.28  Cooper               : 0.00
% 2.03/1.28  Total                : 0.48
% 2.03/1.28  Index Insertion      : 0.00
% 2.03/1.28  Index Deletion       : 0.00
% 2.03/1.28  Index Matching       : 0.00
% 2.03/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
