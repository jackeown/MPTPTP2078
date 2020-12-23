%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:43 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   52 (  58 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 (  84 expanded)
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

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_33,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_39,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_57,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_61,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_43,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k1_relat_1(B_37),A_38)
      | ~ v4_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [B_47,A_48] :
      ( k2_xboole_0(k1_relat_1(B_47),A_48) = A_48
      | ~ v4_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_xboole_0(A_3,B_4)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [A_52,B_53,A_54] :
      ( r1_xboole_0(A_52,k1_relat_1(B_53))
      | ~ r1_xboole_0(A_52,A_54)
      | ~ v4_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_8])).

tff(c_97,plain,(
    ! [B_55] :
      ( r1_xboole_0('#skF_2',k1_relat_1(B_55))
      | ~ v4_relat_1(B_55,'#skF_3')
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_18,plain,(
    ! [A_13,B_15] :
      ( k7_relat_1(A_13,B_15) = k1_xboole_0
      | ~ r1_xboole_0(B_15,k1_relat_1(A_13))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_105,plain,(
    ! [B_56] :
      ( k7_relat_1(B_56,'#skF_2') = k1_xboole_0
      | ~ v4_relat_1(B_56,'#skF_3')
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_97,c_18])).

tff(c_108,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_105])).

tff(c_111,plain,(
    k7_relat_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_108])).

tff(c_116,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( k5_relset_1(A_57,B_58,C_59,D_60) = k7_relat_1(C_59,D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    ! [D_60] : k5_relset_1('#skF_3','#skF_1','#skF_4',D_60) = k7_relat_1('#skF_4',D_60) ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_26,plain,(
    k5_relset_1('#skF_3','#skF_1','#skF_4','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,(
    k7_relat_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_26])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:01 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.23  %$ v5_relat_1 > v4_relat_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.23  
% 2.02/1.23  %Foreground sorts:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Background operators:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Foreground operators:
% 2.02/1.23  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.02/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.02/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.23  
% 2.02/1.25  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.02/1.25  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.02/1.25  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.02/1.25  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.02/1.25  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.02/1.25  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.02/1.25  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.02/1.25  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 2.02/1.25  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.02/1.25  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.02/1.25  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.25  tff(c_33, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.25  tff(c_36, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_33])).
% 2.02/1.25  tff(c_39, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 2.02/1.25  tff(c_57, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.25  tff(c_61, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_57])).
% 2.02/1.25  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.25  tff(c_43, plain, (![B_37, A_38]: (r1_tarski(k1_relat_1(B_37), A_38) | ~v4_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.25  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.25  tff(c_63, plain, (![B_47, A_48]: (k2_xboole_0(k1_relat_1(B_47), A_48)=A_48 | ~v4_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_43, c_2])).
% 2.02/1.25  tff(c_8, plain, (![A_3, B_4, C_5]: (r1_xboole_0(A_3, B_4) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.25  tff(c_90, plain, (![A_52, B_53, A_54]: (r1_xboole_0(A_52, k1_relat_1(B_53)) | ~r1_xboole_0(A_52, A_54) | ~v4_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_63, c_8])).
% 2.02/1.25  tff(c_97, plain, (![B_55]: (r1_xboole_0('#skF_2', k1_relat_1(B_55)) | ~v4_relat_1(B_55, '#skF_3') | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_28, c_90])).
% 2.02/1.25  tff(c_18, plain, (![A_13, B_15]: (k7_relat_1(A_13, B_15)=k1_xboole_0 | ~r1_xboole_0(B_15, k1_relat_1(A_13)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.25  tff(c_105, plain, (![B_56]: (k7_relat_1(B_56, '#skF_2')=k1_xboole_0 | ~v4_relat_1(B_56, '#skF_3') | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_97, c_18])).
% 2.02/1.25  tff(c_108, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_61, c_105])).
% 2.02/1.25  tff(c_111, plain, (k7_relat_1('#skF_4', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_39, c_108])).
% 2.02/1.25  tff(c_116, plain, (![A_57, B_58, C_59, D_60]: (k5_relset_1(A_57, B_58, C_59, D_60)=k7_relat_1(C_59, D_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.25  tff(c_119, plain, (![D_60]: (k5_relset_1('#skF_3', '#skF_1', '#skF_4', D_60)=k7_relat_1('#skF_4', D_60))), inference(resolution, [status(thm)], [c_30, c_116])).
% 2.02/1.25  tff(c_26, plain, (k5_relset_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.25  tff(c_120, plain, (k7_relat_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_26])).
% 2.02/1.25  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_120])).
% 2.02/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  Inference rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Ref     : 0
% 2.02/1.25  #Sup     : 20
% 2.02/1.25  #Fact    : 0
% 2.02/1.25  #Define  : 0
% 2.02/1.25  #Split   : 0
% 2.02/1.25  #Chain   : 0
% 2.02/1.25  #Close   : 0
% 2.02/1.25  
% 2.02/1.25  Ordering : KBO
% 2.02/1.25  
% 2.02/1.25  Simplification rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Subsume      : 0
% 2.02/1.25  #Demod        : 4
% 2.02/1.25  #Tautology    : 9
% 2.02/1.25  #SimpNegUnit  : 0
% 2.02/1.25  #BackRed      : 1
% 2.02/1.25  
% 2.02/1.25  #Partial instantiations: 0
% 2.02/1.25  #Strategies tried      : 1
% 2.02/1.25  
% 2.02/1.25  Timing (in seconds)
% 2.02/1.25  ----------------------
% 2.02/1.25  Preprocessing        : 0.29
% 2.02/1.25  Parsing              : 0.16
% 2.02/1.25  CNF conversion       : 0.02
% 2.02/1.25  Main loop            : 0.18
% 2.02/1.25  Inferencing          : 0.08
% 2.02/1.25  Reduction            : 0.05
% 2.02/1.25  Demodulation         : 0.04
% 2.02/1.25  BG Simplification    : 0.01
% 2.02/1.25  Subsumption          : 0.03
% 2.02/1.25  Abstraction          : 0.01
% 2.02/1.25  MUC search           : 0.00
% 2.02/1.25  Cooper               : 0.00
% 2.02/1.25  Total                : 0.51
% 2.02/1.25  Index Insertion      : 0.00
% 2.02/1.25  Index Deletion       : 0.00
% 2.02/1.25  Index Matching       : 0.00
% 2.02/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
