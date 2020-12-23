%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 128 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(m1_funct_2,type,(
    m1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => m1_funct_2(k1_funct_2(A,B),A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_74,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1('#skF_1'(A_40,B_41,C_42),C_42)
      | m1_funct_2(C_42,A_40,B_41)
      | v1_xboole_0(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39,plain,(
    ! [B_23,A_24] :
      ( r2_hidden(B_23,A_24)
      | ~ m1_subset_1(B_23,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_funct_1(C_13)
      | ~ r2_hidden(C_13,k1_funct_2(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ! [B_23,A_11,B_12] :
      ( v1_funct_1(B_23)
      | ~ m1_subset_1(B_23,k1_funct_2(A_11,B_12))
      | v1_xboole_0(k1_funct_2(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_39,c_26])).

tff(c_84,plain,(
    ! [A_40,B_41,A_11,B_12] :
      ( v1_funct_1('#skF_1'(A_40,B_41,k1_funct_2(A_11,B_12)))
      | m1_funct_2(k1_funct_2(A_11,B_12),A_40,B_41)
      | v1_xboole_0(k1_funct_2(A_11,B_12)) ) ),
    inference(resolution,[status(thm)],[c_74,c_44])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1('#skF_1'(A_3,B_4,C_5),C_5)
      | m1_funct_2(C_5,A_3,B_4)
      | v1_xboole_0(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_funct_2(C_27,A_28,B_29)
      | ~ r2_hidden(C_27,k1_funct_2(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_108,plain,(
    ! [B_54,A_55,B_56] :
      ( v1_funct_2(B_54,A_55,B_56)
      | ~ m1_subset_1(B_54,k1_funct_2(A_55,B_56))
      | v1_xboole_0(k1_funct_2(A_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_117,plain,(
    ! [A_3,B_4,A_55,B_56] :
      ( v1_funct_2('#skF_1'(A_3,B_4,k1_funct_2(A_55,B_56)),A_55,B_56)
      | m1_funct_2(k1_funct_2(A_55,B_56),A_3,B_4)
      | v1_xboole_0(k1_funct_2(A_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_12,c_108])).

tff(c_22,plain,(
    ! [C_13,A_11,B_12] :
      ( m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ r2_hidden(C_13,k1_funct_2(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_121,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ m1_subset_1('#skF_1'(A_67,B_68,C_69),k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2('#skF_1'(A_67,B_68,C_69),A_67,B_68)
      | ~ v1_funct_1('#skF_1'(A_67,B_68,C_69))
      | m1_funct_2(C_69,A_67,B_68)
      | v1_xboole_0(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_160,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ v1_funct_2('#skF_1'(A_98,B_99,C_100),A_98,B_99)
      | ~ v1_funct_1('#skF_1'(A_98,B_99,C_100))
      | m1_funct_2(C_100,A_98,B_99)
      | v1_xboole_0(C_100)
      | ~ r2_hidden('#skF_1'(A_98,B_99,C_100),k1_funct_2(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_22,c_121])).

tff(c_182,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ v1_funct_2('#skF_1'(A_115,B_116,C_117),A_115,B_116)
      | ~ v1_funct_1('#skF_1'(A_115,B_116,C_117))
      | m1_funct_2(C_117,A_115,B_116)
      | v1_xboole_0(C_117)
      | ~ m1_subset_1('#skF_1'(A_115,B_116,C_117),k1_funct_2(A_115,B_116))
      | v1_xboole_0(k1_funct_2(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_192,plain,(
    ! [A_118,B_119] :
      ( ~ v1_funct_2('#skF_1'(A_118,B_119,k1_funct_2(A_118,B_119)),A_118,B_119)
      | ~ v1_funct_1('#skF_1'(A_118,B_119,k1_funct_2(A_118,B_119)))
      | m1_funct_2(k1_funct_2(A_118,B_119),A_118,B_119)
      | v1_xboole_0(k1_funct_2(A_118,B_119)) ) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_203,plain,(
    ! [A_120,B_121] :
      ( ~ v1_funct_1('#skF_1'(A_120,B_121,k1_funct_2(A_120,B_121)))
      | m1_funct_2(k1_funct_2(A_120,B_121),A_120,B_121)
      | v1_xboole_0(k1_funct_2(A_120,B_121)) ) ),
    inference(resolution,[status(thm)],[c_117,c_192])).

tff(c_209,plain,(
    ! [A_122,B_123] :
      ( m1_funct_2(k1_funct_2(A_122,B_123),A_122,B_123)
      | v1_xboole_0(k1_funct_2(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_84,c_203])).

tff(c_28,plain,(
    ~ m1_funct_2(k1_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_216,plain,(
    v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_209,c_28])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( ~ v1_xboole_0(k1_funct_2(A_9,B_10))
      | v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_220,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_216,c_20])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.65  
% 2.63/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.66  %$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.63/1.66  
% 2.63/1.66  %Foreground sorts:
% 2.63/1.66  
% 2.63/1.66  
% 2.63/1.66  %Background operators:
% 2.63/1.66  
% 2.63/1.66  
% 2.63/1.66  %Foreground operators:
% 2.63/1.66  tff(m1_funct_2, type, m1_funct_2: ($i * $i * $i) > $o).
% 2.63/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.63/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.63/1.66  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.66  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 2.63/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.66  
% 2.63/1.67  tff(f_72, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => m1_funct_2(k1_funct_2(A, B), A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_funct_2)).
% 2.63/1.67  tff(f_52, axiom, (![A, B, C]: (~v1_xboole_0(C) => (m1_funct_2(C, A, B) <=> (![D]: (m1_subset_1(D, C) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_2)).
% 2.63/1.67  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.63/1.67  tff(f_66, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 2.63/1.67  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => ~v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_funct_2)).
% 2.63/1.67  tff(c_30, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.63/1.67  tff(c_74, plain, (![A_40, B_41, C_42]: (m1_subset_1('#skF_1'(A_40, B_41, C_42), C_42) | m1_funct_2(C_42, A_40, B_41) | v1_xboole_0(C_42))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.67  tff(c_39, plain, (![B_23, A_24]: (r2_hidden(B_23, A_24) | ~m1_subset_1(B_23, A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.63/1.67  tff(c_26, plain, (![C_13, A_11, B_12]: (v1_funct_1(C_13) | ~r2_hidden(C_13, k1_funct_2(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.63/1.67  tff(c_44, plain, (![B_23, A_11, B_12]: (v1_funct_1(B_23) | ~m1_subset_1(B_23, k1_funct_2(A_11, B_12)) | v1_xboole_0(k1_funct_2(A_11, B_12)))), inference(resolution, [status(thm)], [c_39, c_26])).
% 2.63/1.67  tff(c_84, plain, (![A_40, B_41, A_11, B_12]: (v1_funct_1('#skF_1'(A_40, B_41, k1_funct_2(A_11, B_12))) | m1_funct_2(k1_funct_2(A_11, B_12), A_40, B_41) | v1_xboole_0(k1_funct_2(A_11, B_12)))), inference(resolution, [status(thm)], [c_74, c_44])).
% 2.63/1.67  tff(c_12, plain, (![A_3, B_4, C_5]: (m1_subset_1('#skF_1'(A_3, B_4, C_5), C_5) | m1_funct_2(C_5, A_3, B_4) | v1_xboole_0(C_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.67  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.63/1.67  tff(c_50, plain, (![C_27, A_28, B_29]: (v1_funct_2(C_27, A_28, B_29) | ~r2_hidden(C_27, k1_funct_2(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.63/1.67  tff(c_108, plain, (![B_54, A_55, B_56]: (v1_funct_2(B_54, A_55, B_56) | ~m1_subset_1(B_54, k1_funct_2(A_55, B_56)) | v1_xboole_0(k1_funct_2(A_55, B_56)))), inference(resolution, [status(thm)], [c_4, c_50])).
% 2.63/1.67  tff(c_117, plain, (![A_3, B_4, A_55, B_56]: (v1_funct_2('#skF_1'(A_3, B_4, k1_funct_2(A_55, B_56)), A_55, B_56) | m1_funct_2(k1_funct_2(A_55, B_56), A_3, B_4) | v1_xboole_0(k1_funct_2(A_55, B_56)))), inference(resolution, [status(thm)], [c_12, c_108])).
% 2.63/1.67  tff(c_22, plain, (![C_13, A_11, B_12]: (m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~r2_hidden(C_13, k1_funct_2(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.63/1.67  tff(c_121, plain, (![A_67, B_68, C_69]: (~m1_subset_1('#skF_1'(A_67, B_68, C_69), k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2('#skF_1'(A_67, B_68, C_69), A_67, B_68) | ~v1_funct_1('#skF_1'(A_67, B_68, C_69)) | m1_funct_2(C_69, A_67, B_68) | v1_xboole_0(C_69))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.67  tff(c_160, plain, (![A_98, B_99, C_100]: (~v1_funct_2('#skF_1'(A_98, B_99, C_100), A_98, B_99) | ~v1_funct_1('#skF_1'(A_98, B_99, C_100)) | m1_funct_2(C_100, A_98, B_99) | v1_xboole_0(C_100) | ~r2_hidden('#skF_1'(A_98, B_99, C_100), k1_funct_2(A_98, B_99)))), inference(resolution, [status(thm)], [c_22, c_121])).
% 2.63/1.67  tff(c_182, plain, (![A_115, B_116, C_117]: (~v1_funct_2('#skF_1'(A_115, B_116, C_117), A_115, B_116) | ~v1_funct_1('#skF_1'(A_115, B_116, C_117)) | m1_funct_2(C_117, A_115, B_116) | v1_xboole_0(C_117) | ~m1_subset_1('#skF_1'(A_115, B_116, C_117), k1_funct_2(A_115, B_116)) | v1_xboole_0(k1_funct_2(A_115, B_116)))), inference(resolution, [status(thm)], [c_4, c_160])).
% 2.63/1.67  tff(c_192, plain, (![A_118, B_119]: (~v1_funct_2('#skF_1'(A_118, B_119, k1_funct_2(A_118, B_119)), A_118, B_119) | ~v1_funct_1('#skF_1'(A_118, B_119, k1_funct_2(A_118, B_119))) | m1_funct_2(k1_funct_2(A_118, B_119), A_118, B_119) | v1_xboole_0(k1_funct_2(A_118, B_119)))), inference(resolution, [status(thm)], [c_12, c_182])).
% 2.63/1.67  tff(c_203, plain, (![A_120, B_121]: (~v1_funct_1('#skF_1'(A_120, B_121, k1_funct_2(A_120, B_121))) | m1_funct_2(k1_funct_2(A_120, B_121), A_120, B_121) | v1_xboole_0(k1_funct_2(A_120, B_121)))), inference(resolution, [status(thm)], [c_117, c_192])).
% 2.63/1.67  tff(c_209, plain, (![A_122, B_123]: (m1_funct_2(k1_funct_2(A_122, B_123), A_122, B_123) | v1_xboole_0(k1_funct_2(A_122, B_123)))), inference(resolution, [status(thm)], [c_84, c_203])).
% 2.63/1.67  tff(c_28, plain, (~m1_funct_2(k1_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.63/1.67  tff(c_216, plain, (v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_209, c_28])).
% 2.63/1.67  tff(c_20, plain, (![A_9, B_10]: (~v1_xboole_0(k1_funct_2(A_9, B_10)) | v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.67  tff(c_220, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_216, c_20])).
% 2.63/1.67  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_220])).
% 2.63/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.67  
% 2.63/1.67  Inference rules
% 2.63/1.67  ----------------------
% 2.63/1.67  #Ref     : 0
% 2.63/1.67  #Sup     : 39
% 2.63/1.67  #Fact    : 0
% 2.63/1.67  #Define  : 0
% 2.63/1.67  #Split   : 0
% 2.63/1.67  #Chain   : 0
% 2.63/1.67  #Close   : 0
% 2.63/1.67  
% 2.63/1.67  Ordering : KBO
% 2.63/1.67  
% 2.63/1.67  Simplification rules
% 2.63/1.67  ----------------------
% 2.63/1.67  #Subsume      : 6
% 2.63/1.67  #Demod        : 0
% 2.63/1.67  #Tautology    : 13
% 2.63/1.67  #SimpNegUnit  : 1
% 2.63/1.67  #BackRed      : 0
% 2.63/1.67  
% 2.63/1.67  #Partial instantiations: 0
% 2.63/1.67  #Strategies tried      : 1
% 2.63/1.67  
% 2.63/1.67  Timing (in seconds)
% 2.63/1.67  ----------------------
% 2.63/1.67  Preprocessing        : 0.43
% 2.63/1.67  Parsing              : 0.24
% 2.63/1.67  CNF conversion       : 0.03
% 2.63/1.67  Main loop            : 0.34
% 2.63/1.67  Inferencing          : 0.17
% 2.63/1.67  Reduction            : 0.05
% 2.63/1.67  Demodulation         : 0.02
% 2.63/1.67  BG Simplification    : 0.02
% 2.63/1.67  Subsumption          : 0.08
% 2.63/1.67  Abstraction          : 0.01
% 2.63/1.67  MUC search           : 0.00
% 2.63/1.67  Cooper               : 0.00
% 2.63/1.67  Total                : 0.81
% 2.63/1.67  Index Insertion      : 0.00
% 2.63/1.67  Index Deletion       : 0.00
% 2.63/1.67  Index Matching       : 0.00
% 2.63/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
