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
% DateTime   : Thu Dec  3 10:18:17 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   59 (  88 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 214 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_39,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_39])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    ! [C_24,A_25,B_26] :
      ( v4_relat_1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_61,plain,(
    ! [B_35,A_36] :
      ( k1_relat_1(B_35) = A_36
      | ~ v1_partfun1(B_35,A_36)
      | ~ v4_relat_1(B_35,A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_61])).

tff(c_67,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_64])).

tff(c_68,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_77,plain,(
    ! [B_43,C_44,A_45] :
      ( k1_xboole_0 = B_43
      | v1_partfun1(C_44,A_45)
      | ~ v1_funct_2(C_44,A_45,B_43)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_43)))
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_83,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_80])).

tff(c_84,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_83])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_87,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_87])).

tff(c_90,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_103,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1(k5_relat_1(A_48,B_49)) = k1_relat_1(A_48)
      | ~ r1_tarski(k2_relat_1(A_48),k1_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_48] :
      ( k1_relat_1(k5_relat_1(A_48,'#skF_2')) = k1_relat_1(A_48)
      | ~ r1_tarski(k2_relat_1(A_48),'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_103])).

tff(c_114,plain,(
    ! [A_50] :
      ( k1_relat_1(k5_relat_1(A_50,'#skF_2')) = k1_relat_1(A_50)
      | ~ r1_tarski(k2_relat_1(A_50),'#skF_1')
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_106])).

tff(c_120,plain,(
    ! [B_51] :
      ( k1_relat_1(k5_relat_1(B_51,'#skF_2')) = k1_relat_1(B_51)
      | ~ v5_relat_1(B_51,'#skF_1')
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_24,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_132,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_24])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.26  
% 2.05/1.26  %Foreground sorts:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Background operators:
% 2.05/1.26  
% 2.05/1.26  
% 2.05/1.26  %Foreground operators:
% 2.05/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.05/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.05/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.05/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.05/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.05/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.05/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.26  
% 2.05/1.27  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 2.05/1.27  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.05/1.27  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.05/1.27  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.05/1.27  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.05/1.27  tff(f_76, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.05/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.05/1.27  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.05/1.27  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.05/1.27  tff(c_28, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.05/1.27  tff(c_6, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.27  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.05/1.27  tff(c_39, plain, (![C_21, A_22, B_23]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.27  tff(c_43, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_39])).
% 2.05/1.27  tff(c_38, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.05/1.27  tff(c_44, plain, (![C_24, A_25, B_26]: (v4_relat_1(C_24, A_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_48, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_44])).
% 2.05/1.27  tff(c_61, plain, (![B_35, A_36]: (k1_relat_1(B_35)=A_36 | ~v1_partfun1(B_35, A_36) | ~v4_relat_1(B_35, A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.05/1.27  tff(c_64, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_61])).
% 2.05/1.27  tff(c_67, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_64])).
% 2.05/1.27  tff(c_68, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_67])).
% 2.05/1.27  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.05/1.27  tff(c_34, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.05/1.27  tff(c_77, plain, (![B_43, C_44, A_45]: (k1_xboole_0=B_43 | v1_partfun1(C_44, A_45) | ~v1_funct_2(C_44, A_45, B_43) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_43))) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.05/1.27  tff(c_80, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_77])).
% 2.05/1.27  tff(c_83, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_80])).
% 2.05/1.27  tff(c_84, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_83])).
% 2.05/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.05/1.27  tff(c_87, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2])).
% 2.05/1.27  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_87])).
% 2.05/1.27  tff(c_90, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_67])).
% 2.05/1.27  tff(c_103, plain, (![A_48, B_49]: (k1_relat_1(k5_relat_1(A_48, B_49))=k1_relat_1(A_48) | ~r1_tarski(k2_relat_1(A_48), k1_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.27  tff(c_106, plain, (![A_48]: (k1_relat_1(k5_relat_1(A_48, '#skF_2'))=k1_relat_1(A_48) | ~r1_tarski(k2_relat_1(A_48), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_90, c_103])).
% 2.05/1.27  tff(c_114, plain, (![A_50]: (k1_relat_1(k5_relat_1(A_50, '#skF_2'))=k1_relat_1(A_50) | ~r1_tarski(k2_relat_1(A_50), '#skF_1') | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_106])).
% 2.05/1.27  tff(c_120, plain, (![B_51]: (k1_relat_1(k5_relat_1(B_51, '#skF_2'))=k1_relat_1(B_51) | ~v5_relat_1(B_51, '#skF_1') | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_6, c_114])).
% 2.05/1.27  tff(c_24, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.05/1.27  tff(c_132, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_120, c_24])).
% 2.05/1.27  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_132])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 18
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 1
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 0
% 2.05/1.27  #Demod        : 15
% 2.05/1.27  #Tautology    : 5
% 2.05/1.27  #SimpNegUnit  : 2
% 2.05/1.27  #BackRed      : 3
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.27  Preprocessing        : 0.30
% 2.05/1.27  Parsing              : 0.17
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.16
% 2.05/1.27  Inferencing          : 0.06
% 2.05/1.27  Reduction            : 0.05
% 2.05/1.27  Demodulation         : 0.03
% 2.05/1.27  BG Simplification    : 0.01
% 2.05/1.27  Subsumption          : 0.02
% 2.05/1.27  Abstraction          : 0.01
% 2.05/1.27  MUC search           : 0.00
% 2.05/1.27  Cooper               : 0.00
% 2.05/1.27  Total                : 0.48
% 2.05/1.27  Index Insertion      : 0.00
% 2.05/1.27  Index Deletion       : 0.00
% 2.05/1.27  Index Matching       : 0.00
% 2.05/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
