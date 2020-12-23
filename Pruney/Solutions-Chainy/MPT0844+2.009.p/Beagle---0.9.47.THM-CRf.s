%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:41 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 (  78 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_38,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_38])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(k1_relat_1(B_40),A_41)
      | ~ v4_relat_1(B_40,A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [B_47,A_48] :
      ( k2_xboole_0(k1_relat_1(B_47),A_48) = A_48
      | ~ v4_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_49,B_50,A_51] :
      ( r1_xboole_0(A_49,k1_relat_1(B_50))
      | ~ r1_xboole_0(A_49,A_51)
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_8])).

tff(c_92,plain,(
    ! [B_52] :
      ( r1_xboole_0('#skF_2',k1_relat_1(B_52))
      | ~ v4_relat_1(B_52,'#skF_3')
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k7_relat_1(A_8,B_10) = k1_xboole_0
      | ~ r1_xboole_0(B_10,k1_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,(
    ! [B_53] :
      ( k7_relat_1(B_53,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_53,'#skF_3')
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_92,c_14])).

tff(c_103,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_100])).

tff(c_106,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_103])).

tff(c_111,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k5_relset_1(A_54,B_55,C_56,D_57) = k7_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_114,plain,(
    ! [D_57] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_57) = k7_relat_1('#skF_4',D_57) ),
    inference(resolution,[status(thm)],[c_28,c_111])).

tff(c_24,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_115,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_24])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:32:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.32  
% 2.07/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.33  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.33  
% 2.07/1.33  %Foreground sorts:
% 2.07/1.33  
% 2.07/1.33  
% 2.07/1.33  %Background operators:
% 2.07/1.33  
% 2.07/1.33  
% 2.07/1.33  %Foreground operators:
% 2.07/1.33  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.07/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.07/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.07/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.07/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.33  
% 2.07/1.34  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relset_1)).
% 2.07/1.34  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.07/1.34  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.07/1.34  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.07/1.34  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.07/1.34  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.07/1.34  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.07/1.34  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.07/1.34  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.34  tff(c_30, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.34  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_30])).
% 2.07/1.34  tff(c_38, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.34  tff(c_42, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_38])).
% 2.07/1.34  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.34  tff(c_48, plain, (![B_40, A_41]: (r1_tarski(k1_relat_1(B_40), A_41) | ~v4_relat_1(B_40, A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.34  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.34  tff(c_67, plain, (![B_47, A_48]: (k2_xboole_0(k1_relat_1(B_47), A_48)=A_48 | ~v4_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_48, c_2])).
% 2.07/1.34  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.34  tff(c_85, plain, (![A_49, B_50, A_51]: (r1_xboole_0(A_49, k1_relat_1(B_50)) | ~r1_xboole_0(A_49, A_51) | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_67, c_8])).
% 2.07/1.34  tff(c_92, plain, (![B_52]: (r1_xboole_0('#skF_2', k1_relat_1(B_52)) | ~v4_relat_1(B_52, '#skF_3') | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.07/1.34  tff(c_14, plain, (![A_8, B_10]: (k7_relat_1(A_8, B_10)=k1_xboole_0 | ~r1_xboole_0(B_10, k1_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.34  tff(c_100, plain, (![B_53]: (k7_relat_1(B_53, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_53, '#skF_3') | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_92, c_14])).
% 2.07/1.34  tff(c_103, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_100])).
% 2.07/1.34  tff(c_106, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_103])).
% 2.07/1.34  tff(c_111, plain, (![A_54, B_55, C_56, D_57]: (k5_relset_1(A_54, B_55, C_56, D_57)=k7_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.34  tff(c_114, plain, (![D_57]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_57)=k7_relat_1('#skF_4', D_57))), inference(resolution, [status(thm)], [c_28, c_111])).
% 2.07/1.34  tff(c_24, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.34  tff(c_115, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_24])).
% 2.07/1.34  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_115])).
% 2.07/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.34  
% 2.07/1.34  Inference rules
% 2.07/1.34  ----------------------
% 2.07/1.34  #Ref     : 0
% 2.07/1.34  #Sup     : 20
% 2.07/1.34  #Fact    : 0
% 2.07/1.34  #Define  : 0
% 2.07/1.34  #Split   : 0
% 2.07/1.34  #Chain   : 0
% 2.07/1.34  #Close   : 0
% 2.07/1.34  
% 2.07/1.34  Ordering : KBO
% 2.07/1.34  
% 2.07/1.34  Simplification rules
% 2.07/1.34  ----------------------
% 2.07/1.34  #Subsume      : 0
% 2.07/1.34  #Demod        : 3
% 2.07/1.34  #Tautology    : 9
% 2.07/1.34  #SimpNegUnit  : 0
% 2.07/1.34  #BackRed      : 1
% 2.07/1.34  
% 2.07/1.34  #Partial instantiations: 0
% 2.07/1.34  #Strategies tried      : 1
% 2.07/1.34  
% 2.07/1.34  Timing (in seconds)
% 2.07/1.34  ----------------------
% 2.07/1.34  Preprocessing        : 0.37
% 2.07/1.34  Parsing              : 0.18
% 2.07/1.34  CNF conversion       : 0.02
% 2.07/1.34  Main loop            : 0.13
% 2.07/1.34  Inferencing          : 0.05
% 2.07/1.34  Reduction            : 0.04
% 2.07/1.34  Demodulation         : 0.03
% 2.07/1.34  BG Simplification    : 0.01
% 2.07/1.34  Subsumption          : 0.02
% 2.07/1.34  Abstraction          : 0.01
% 2.07/1.34  MUC search           : 0.00
% 2.07/1.34  Cooper               : 0.00
% 2.07/1.34  Total                : 0.53
% 2.07/1.34  Index Insertion      : 0.00
% 2.07/1.34  Index Deletion       : 0.00
% 2.07/1.34  Index Matching       : 0.00
% 2.07/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
