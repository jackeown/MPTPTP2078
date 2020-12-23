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
% DateTime   : Thu Dec  3 10:15:48 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 104 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 345 expanded)
%              Number of equality atoms :   26 (  94 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_18,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [C_21,B_22,A_23] :
      ( ~ v1_xboole_0(C_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_21))
      | ~ r2_hidden(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [B_28,A_29,A_30] :
      ( ~ v1_xboole_0(B_28)
      | ~ r2_hidden(A_29,A_30)
      | ~ r1_tarski(A_30,B_28) ) ),
    inference(resolution,[status(thm)],[c_12,c_59])).

tff(c_81,plain,(
    ! [B_31] :
      ( ~ v1_xboole_0(B_31)
      | ~ r1_tarski('#skF_1',B_31) ) ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_66,plain,(
    ! [D_24,C_25,B_26,A_27] :
      ( k1_funct_1(k2_funct_1(D_24),k1_funct_1(D_24,C_25)) = C_25
      | k1_xboole_0 = B_26
      | ~ r2_hidden(C_25,A_27)
      | ~ v2_funct_1(D_24)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_27,B_26)))
      | ~ v1_funct_2(D_24,A_27,B_26)
      | ~ v1_funct_1(D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,(
    ! [D_32,B_33] :
      ( k1_funct_1(k2_funct_1(D_32),k1_funct_1(D_32,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_33
      | ~ v2_funct_1(D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_33)))
      | ~ v1_funct_2(D_32,'#skF_1',B_33)
      | ~ v1_funct_1(D_32) ) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_93,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_88])).

tff(c_97,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_93])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_112,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_112])).

tff(c_115,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_116,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_20,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_98,plain,(
    ! [D_34,B_35] :
      ( k1_funct_1(k2_funct_1(D_34),k1_funct_1(D_34,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_35
      | ~ v2_funct_1(D_34)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_35)))
      | ~ v1_funct_2(D_34,'#skF_1',B_35)
      | ~ v1_funct_1(D_34) ) ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_103,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_107,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_20,c_103])).

tff(c_117,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_107])).

tff(c_122,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_117])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.28  
% 2.11/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.28  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.11/1.28  
% 2.11/1.28  %Foreground sorts:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Background operators:
% 2.11/1.28  
% 2.11/1.28  
% 2.11/1.28  %Foreground operators:
% 2.11/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.11/1.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.28  
% 2.11/1.29  tff(f_75, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.11/1.29  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.11/1.29  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.11/1.29  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.11/1.29  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.11/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.11/1.29  tff(c_18, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.11/1.29  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.11/1.29  tff(c_59, plain, (![C_21, B_22, A_23]: (~v1_xboole_0(C_21) | ~m1_subset_1(B_22, k1_zfmisc_1(C_21)) | ~r2_hidden(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.29  tff(c_74, plain, (![B_28, A_29, A_30]: (~v1_xboole_0(B_28) | ~r2_hidden(A_29, A_30) | ~r1_tarski(A_30, B_28))), inference(resolution, [status(thm)], [c_12, c_59])).
% 2.11/1.29  tff(c_81, plain, (![B_31]: (~v1_xboole_0(B_31) | ~r1_tarski('#skF_1', B_31))), inference(resolution, [status(thm)], [c_22, c_74])).
% 2.11/1.29  tff(c_86, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_81])).
% 2.11/1.29  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_30, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_26, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_66, plain, (![D_24, C_25, B_26, A_27]: (k1_funct_1(k2_funct_1(D_24), k1_funct_1(D_24, C_25))=C_25 | k1_xboole_0=B_26 | ~r2_hidden(C_25, A_27) | ~v2_funct_1(D_24) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_27, B_26))) | ~v1_funct_2(D_24, A_27, B_26) | ~v1_funct_1(D_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.29  tff(c_88, plain, (![D_32, B_33]: (k1_funct_1(k2_funct_1(D_32), k1_funct_1(D_32, '#skF_4'))='#skF_4' | k1_xboole_0=B_33 | ~v2_funct_1(D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_33))) | ~v1_funct_2(D_32, '#skF_1', B_33) | ~v1_funct_1(D_32))), inference(resolution, [status(thm)], [c_22, c_66])).
% 2.11/1.29  tff(c_93, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_88])).
% 2.11/1.29  tff(c_97, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_93])).
% 2.11/1.29  tff(c_108, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_97])).
% 2.11/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.11/1.29  tff(c_112, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2])).
% 2.11/1.29  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_112])).
% 2.11/1.29  tff(c_115, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_97])).
% 2.11/1.29  tff(c_116, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_97])).
% 2.11/1.29  tff(c_20, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.11/1.29  tff(c_98, plain, (![D_34, B_35]: (k1_funct_1(k2_funct_1(D_34), k1_funct_1(D_34, '#skF_3'))='#skF_3' | k1_xboole_0=B_35 | ~v2_funct_1(D_34) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_35))) | ~v1_funct_2(D_34, '#skF_1', B_35) | ~v1_funct_1(D_34))), inference(resolution, [status(thm)], [c_24, c_66])).
% 2.11/1.29  tff(c_103, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_98])).
% 2.11/1.29  tff(c_107, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_20, c_103])).
% 2.11/1.29  tff(c_117, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_116, c_107])).
% 2.11/1.29  tff(c_122, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_117])).
% 2.11/1.29  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_122])).
% 2.11/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  Inference rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Ref     : 0
% 2.11/1.29  #Sup     : 19
% 2.11/1.29  #Fact    : 0
% 2.11/1.29  #Define  : 0
% 2.11/1.29  #Split   : 3
% 2.11/1.29  #Chain   : 0
% 2.11/1.29  #Close   : 0
% 2.11/1.29  
% 2.11/1.29  Ordering : KBO
% 2.11/1.29  
% 2.11/1.29  Simplification rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Subsume      : 1
% 2.11/1.29  #Demod        : 14
% 2.11/1.29  #Tautology    : 7
% 2.11/1.29  #SimpNegUnit  : 3
% 2.11/1.29  #BackRed      : 5
% 2.11/1.29  
% 2.11/1.29  #Partial instantiations: 0
% 2.11/1.29  #Strategies tried      : 1
% 2.11/1.29  
% 2.11/1.29  Timing (in seconds)
% 2.11/1.29  ----------------------
% 2.11/1.30  Preprocessing        : 0.32
% 2.11/1.30  Parsing              : 0.16
% 2.11/1.30  CNF conversion       : 0.02
% 2.11/1.30  Main loop            : 0.15
% 2.11/1.30  Inferencing          : 0.05
% 2.11/1.30  Reduction            : 0.05
% 2.11/1.30  Demodulation         : 0.04
% 2.11/1.30  BG Simplification    : 0.01
% 2.11/1.30  Subsumption          : 0.02
% 2.11/1.30  Abstraction          : 0.01
% 2.11/1.30  MUC search           : 0.00
% 2.11/1.30  Cooper               : 0.00
% 2.11/1.30  Total                : 0.50
% 2.11/1.30  Index Insertion      : 0.00
% 2.11/1.30  Index Deletion       : 0.00
% 2.11/1.30  Index Matching       : 0.00
% 2.11/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
