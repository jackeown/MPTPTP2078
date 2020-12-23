%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => m1_funct_2(k1_funct_2(A,B),A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_funct_2)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1('#skF_1'(A_3,B_4,C_5),C_5)
      | m1_funct_2(C_5,A_3,B_4)
      | v1_xboole_0(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_29,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_funct_1(C_13)
      | ~ r2_hidden(C_13,k1_funct_2(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [A_38,A_39,B_40] :
      ( v1_funct_1(A_38)
      | v1_xboole_0(k1_funct_2(A_39,B_40))
      | ~ m1_subset_1(A_38,k1_funct_2(A_39,B_40)) ) ),
    inference(resolution,[status(thm)],[c_29,c_20])).

tff(c_64,plain,(
    ! [A_3,B_4,A_39,B_40] :
      ( v1_funct_1('#skF_1'(A_3,B_4,k1_funct_2(A_39,B_40)))
      | m1_funct_2(k1_funct_2(A_39,B_40),A_3,B_4)
      | v1_xboole_0(k1_funct_2(A_39,B_40)) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_funct_2(C_23,A_24,B_25)
      | ~ r2_hidden(C_23,k1_funct_2(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_45,A_46,B_47] :
      ( v1_funct_2(A_45,A_46,B_47)
      | v1_xboole_0(k1_funct_2(A_46,B_47))
      | ~ m1_subset_1(A_45,k1_funct_2(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_77,plain,(
    ! [A_3,B_4,A_46,B_47] :
      ( v1_funct_2('#skF_1'(A_3,B_4,k1_funct_2(A_46,B_47)),A_46,B_47)
      | m1_funct_2(k1_funct_2(A_46,B_47),A_3,B_4)
      | v1_xboole_0(k1_funct_2(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_16,plain,(
    ! [C_13,A_11,B_12] :
      ( m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ r2_hidden(C_13,k1_funct_2(A_11,B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ m1_subset_1('#skF_1'(A_57,B_58,C_59),k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2('#skF_1'(A_57,B_58,C_59),A_57,B_58)
      | ~ v1_funct_1('#skF_1'(A_57,B_58,C_59))
      | m1_funct_2(C_59,A_57,B_58)
      | v1_xboole_0(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ v1_funct_2('#skF_1'(A_88,B_89,C_90),A_88,B_89)
      | ~ v1_funct_1('#skF_1'(A_88,B_89,C_90))
      | m1_funct_2(C_90,A_88,B_89)
      | v1_xboole_0(C_90)
      | ~ r2_hidden('#skF_1'(A_88,B_89,C_90),k1_funct_2(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_129,plain,(
    ! [A_100,B_101,C_102] :
      ( ~ v1_funct_2('#skF_1'(A_100,B_101,C_102),A_100,B_101)
      | ~ v1_funct_1('#skF_1'(A_100,B_101,C_102))
      | m1_funct_2(C_102,A_100,B_101)
      | v1_xboole_0(C_102)
      | v1_xboole_0(k1_funct_2(A_100,B_101))
      | ~ m1_subset_1('#skF_1'(A_100,B_101,C_102),k1_funct_2(A_100,B_101)) ) ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_135,plain,(
    ! [A_103,B_104] :
      ( ~ v1_funct_2('#skF_1'(A_103,B_104,k1_funct_2(A_103,B_104)),A_103,B_104)
      | ~ v1_funct_1('#skF_1'(A_103,B_104,k1_funct_2(A_103,B_104)))
      | m1_funct_2(k1_funct_2(A_103,B_104),A_103,B_104)
      | v1_xboole_0(k1_funct_2(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_146,plain,(
    ! [A_105,B_106] :
      ( ~ v1_funct_1('#skF_1'(A_105,B_106,k1_funct_2(A_105,B_106)))
      | m1_funct_2(k1_funct_2(A_105,B_106),A_105,B_106)
      | v1_xboole_0(k1_funct_2(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_77,c_135])).

tff(c_152,plain,(
    ! [A_107,B_108] :
      ( m1_funct_2(k1_funct_2(A_107,B_108),A_107,B_108)
      | v1_xboole_0(k1_funct_2(A_107,B_108)) ) ),
    inference(resolution,[status(thm)],[c_64,c_146])).

tff(c_24,plain,(
    ~ m1_funct_2(k1_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_159,plain,(
    v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_152,c_24])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( ~ v1_xboole_0(k1_funct_2(A_9,B_10))
      | v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_14])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.21  
% 2.01/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.21  %$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.10/1.21  
% 2.10/1.21  %Foreground sorts:
% 2.10/1.21  
% 2.10/1.21  
% 2.10/1.21  %Background operators:
% 2.10/1.21  
% 2.10/1.21  
% 2.10/1.21  %Foreground operators:
% 2.10/1.21  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 2.10/1.21  tff(m1_funct_2, type, m1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.21  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 2.10/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.21  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.10/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.21  
% 2.10/1.22  tff(f_67, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => m1_funct_2(k1_funct_2(A, B), A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_funct_2)).
% 2.10/1.22  tff(f_45, axiom, (![A, B, C]: (~v1_xboole_0(C) => (m1_funct_2(C, A, B) <=> (![D]: (m1_subset_1(D, C) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_2)).
% 2.10/1.22  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.10/1.22  tff(f_59, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 2.10/1.22  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => ~v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_funct_2)).
% 2.10/1.22  tff(c_26, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.22  tff(c_6, plain, (![A_3, B_4, C_5]: (m1_subset_1('#skF_1'(A_3, B_4, C_5), C_5) | m1_funct_2(C_5, A_3, B_4) | v1_xboole_0(C_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.22  tff(c_29, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.22  tff(c_20, plain, (![C_13, A_11, B_12]: (v1_funct_1(C_13) | ~r2_hidden(C_13, k1_funct_2(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.22  tff(c_59, plain, (![A_38, A_39, B_40]: (v1_funct_1(A_38) | v1_xboole_0(k1_funct_2(A_39, B_40)) | ~m1_subset_1(A_38, k1_funct_2(A_39, B_40)))), inference(resolution, [status(thm)], [c_29, c_20])).
% 2.10/1.22  tff(c_64, plain, (![A_3, B_4, A_39, B_40]: (v1_funct_1('#skF_1'(A_3, B_4, k1_funct_2(A_39, B_40))) | m1_funct_2(k1_funct_2(A_39, B_40), A_3, B_4) | v1_xboole_0(k1_funct_2(A_39, B_40)))), inference(resolution, [status(thm)], [c_6, c_59])).
% 2.10/1.22  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.22  tff(c_35, plain, (![C_23, A_24, B_25]: (v1_funct_2(C_23, A_24, B_25) | ~r2_hidden(C_23, k1_funct_2(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.22  tff(c_72, plain, (![A_45, A_46, B_47]: (v1_funct_2(A_45, A_46, B_47) | v1_xboole_0(k1_funct_2(A_46, B_47)) | ~m1_subset_1(A_45, k1_funct_2(A_46, B_47)))), inference(resolution, [status(thm)], [c_2, c_35])).
% 2.10/1.22  tff(c_77, plain, (![A_3, B_4, A_46, B_47]: (v1_funct_2('#skF_1'(A_3, B_4, k1_funct_2(A_46, B_47)), A_46, B_47) | m1_funct_2(k1_funct_2(A_46, B_47), A_3, B_4) | v1_xboole_0(k1_funct_2(A_46, B_47)))), inference(resolution, [status(thm)], [c_6, c_72])).
% 2.10/1.22  tff(c_16, plain, (![C_13, A_11, B_12]: (m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~r2_hidden(C_13, k1_funct_2(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.22  tff(c_86, plain, (![A_57, B_58, C_59]: (~m1_subset_1('#skF_1'(A_57, B_58, C_59), k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2('#skF_1'(A_57, B_58, C_59), A_57, B_58) | ~v1_funct_1('#skF_1'(A_57, B_58, C_59)) | m1_funct_2(C_59, A_57, B_58) | v1_xboole_0(C_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.22  tff(c_117, plain, (![A_88, B_89, C_90]: (~v1_funct_2('#skF_1'(A_88, B_89, C_90), A_88, B_89) | ~v1_funct_1('#skF_1'(A_88, B_89, C_90)) | m1_funct_2(C_90, A_88, B_89) | v1_xboole_0(C_90) | ~r2_hidden('#skF_1'(A_88, B_89, C_90), k1_funct_2(A_88, B_89)))), inference(resolution, [status(thm)], [c_16, c_86])).
% 2.10/1.22  tff(c_129, plain, (![A_100, B_101, C_102]: (~v1_funct_2('#skF_1'(A_100, B_101, C_102), A_100, B_101) | ~v1_funct_1('#skF_1'(A_100, B_101, C_102)) | m1_funct_2(C_102, A_100, B_101) | v1_xboole_0(C_102) | v1_xboole_0(k1_funct_2(A_100, B_101)) | ~m1_subset_1('#skF_1'(A_100, B_101, C_102), k1_funct_2(A_100, B_101)))), inference(resolution, [status(thm)], [c_2, c_117])).
% 2.10/1.22  tff(c_135, plain, (![A_103, B_104]: (~v1_funct_2('#skF_1'(A_103, B_104, k1_funct_2(A_103, B_104)), A_103, B_104) | ~v1_funct_1('#skF_1'(A_103, B_104, k1_funct_2(A_103, B_104))) | m1_funct_2(k1_funct_2(A_103, B_104), A_103, B_104) | v1_xboole_0(k1_funct_2(A_103, B_104)))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.10/1.22  tff(c_146, plain, (![A_105, B_106]: (~v1_funct_1('#skF_1'(A_105, B_106, k1_funct_2(A_105, B_106))) | m1_funct_2(k1_funct_2(A_105, B_106), A_105, B_106) | v1_xboole_0(k1_funct_2(A_105, B_106)))), inference(resolution, [status(thm)], [c_77, c_135])).
% 2.10/1.22  tff(c_152, plain, (![A_107, B_108]: (m1_funct_2(k1_funct_2(A_107, B_108), A_107, B_108) | v1_xboole_0(k1_funct_2(A_107, B_108)))), inference(resolution, [status(thm)], [c_64, c_146])).
% 2.10/1.22  tff(c_24, plain, (~m1_funct_2(k1_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.22  tff(c_159, plain, (v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_152, c_24])).
% 2.10/1.22  tff(c_14, plain, (![A_9, B_10]: (~v1_xboole_0(k1_funct_2(A_9, B_10)) | v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.22  tff(c_162, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_159, c_14])).
% 2.10/1.22  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_162])).
% 2.10/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.22  
% 2.10/1.22  Inference rules
% 2.10/1.22  ----------------------
% 2.10/1.22  #Ref     : 0
% 2.10/1.22  #Sup     : 27
% 2.10/1.22  #Fact    : 0
% 2.10/1.22  #Define  : 0
% 2.10/1.22  #Split   : 0
% 2.10/1.22  #Chain   : 0
% 2.10/1.22  #Close   : 0
% 2.10/1.22  
% 2.10/1.22  Ordering : KBO
% 2.10/1.22  
% 2.10/1.22  Simplification rules
% 2.10/1.22  ----------------------
% 2.10/1.22  #Subsume      : 5
% 2.10/1.22  #Demod        : 0
% 2.10/1.22  #Tautology    : 5
% 2.10/1.22  #SimpNegUnit  : 1
% 2.10/1.22  #BackRed      : 0
% 2.10/1.22  
% 2.10/1.22  #Partial instantiations: 0
% 2.10/1.22  #Strategies tried      : 1
% 2.10/1.22  
% 2.10/1.22  Timing (in seconds)
% 2.10/1.22  ----------------------
% 2.10/1.23  Preprocessing        : 0.28
% 2.10/1.23  Parsing              : 0.16
% 2.10/1.23  CNF conversion       : 0.02
% 2.10/1.23  Main loop            : 0.19
% 2.10/1.23  Inferencing          : 0.09
% 2.10/1.23  Reduction            : 0.04
% 2.10/1.23  Demodulation         : 0.02
% 2.10/1.23  BG Simplification    : 0.01
% 2.10/1.23  Subsumption          : 0.04
% 2.10/1.23  Abstraction          : 0.01
% 2.10/1.23  MUC search           : 0.00
% 2.10/1.23  Cooper               : 0.00
% 2.10/1.23  Total                : 0.50
% 2.10/1.23  Index Insertion      : 0.00
% 2.10/1.23  Index Deletion       : 0.00
% 2.10/1.23  Index Matching       : 0.00
% 2.10/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
