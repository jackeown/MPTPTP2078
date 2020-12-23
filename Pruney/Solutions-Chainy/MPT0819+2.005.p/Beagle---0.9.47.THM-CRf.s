%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:58 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 114 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 226 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_53,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_170,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_179,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_113,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,'#skF_4')
      | ~ r1_tarski(A_61,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_113])).

tff(c_138,plain,(
    ! [B_7] :
      ( r1_tarski(k2_relat_1(B_7),'#skF_4')
      | ~ v5_relat_1(B_7,'#skF_3')
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_128,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,'#skF_2')
      | ~ r1_tarski(A_58,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_113])).

tff(c_393,plain,(
    ! [C_106,A_107,B_108] :
      ( m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ r1_tarski(k2_relat_1(C_106),B_108)
      | ~ r1_tarski(k1_relat_1(C_106),A_107)
      | ~ v1_relat_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_408,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_393,c_30])).

tff(c_415,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_408])).

tff(c_416,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_415])).

tff(c_420,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_128,c_416])).

tff(c_433,plain,(
    ! [D_122,C_123,B_124,A_125] :
      ( m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(C_123,B_124)))
      | ~ r1_tarski(k2_relat_1(D_122),B_124)
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(C_123,A_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_444,plain,(
    ! [B_126] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_126)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_126) ) ),
    inference(resolution,[status(thm)],[c_36,c_433])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_499,plain,(
    ! [B_128] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_1',B_128))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_128) ) ),
    inference(resolution,[status(thm)],[c_444,c_4])).

tff(c_503,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_1','#skF_4'))
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_138,c_499])).

tff(c_522,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_179,c_503])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_302,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k1_relat_1(A_90),k1_relat_1(B_91))
      | ~ r1_tarski(A_90,B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_10,B_11)),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    ! [A_58,A_10,B_11] :
      ( r1_tarski(A_58,A_10)
      | ~ r1_tarski(A_58,k1_relat_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_306,plain,(
    ! [A_90,A_10,B_11] :
      ( r1_tarski(k1_relat_1(A_90),A_10)
      | ~ r1_tarski(A_90,k2_zfmisc_1(A_10,B_11))
      | ~ v1_relat_1(k2_zfmisc_1(A_10,B_11))
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_302,c_126])).

tff(c_661,plain,(
    ! [A_139,A_140,B_141] :
      ( r1_tarski(k1_relat_1(A_139),A_140)
      | ~ r1_tarski(A_139,k2_zfmisc_1(A_140,B_141))
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_306])).

tff(c_667,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_522,c_661])).

tff(c_688,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_667])).

tff(c_690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_688])).

tff(c_691,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_415])).

tff(c_695,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_138,c_691])).

tff(c_702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_179,c_695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:43:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.45  
% 2.66/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.66/1.45  
% 2.66/1.45  %Foreground sorts:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Background operators:
% 2.66/1.45  
% 2.66/1.45  
% 2.66/1.45  %Foreground operators:
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.66/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.66/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.45  
% 3.00/1.46  tff(f_89, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 3.00/1.46  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.00/1.46  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.00/1.46  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.00/1.46  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.00/1.46  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.00/1.46  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 3.00/1.46  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.00/1.46  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.00/1.46  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.00/1.46  tff(f_45, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 3.00/1.46  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.00/1.46  tff(c_53, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.46  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_53])).
% 3.00/1.46  tff(c_170, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.46  tff(c_179, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_170])).
% 3.00/1.46  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.46  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.00/1.46  tff(c_113, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.46  tff(c_129, plain, (![A_61]: (r1_tarski(A_61, '#skF_4') | ~r1_tarski(A_61, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_113])).
% 3.00/1.46  tff(c_138, plain, (![B_7]: (r1_tarski(k2_relat_1(B_7), '#skF_4') | ~v5_relat_1(B_7, '#skF_3') | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_129])).
% 3.00/1.46  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.00/1.46  tff(c_128, plain, (![A_58]: (r1_tarski(A_58, '#skF_2') | ~r1_tarski(A_58, '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_113])).
% 3.00/1.46  tff(c_393, plain, (![C_106, A_107, B_108]: (m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~r1_tarski(k2_relat_1(C_106), B_108) | ~r1_tarski(k1_relat_1(C_106), A_107) | ~v1_relat_1(C_106))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.00/1.46  tff(c_30, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.00/1.46  tff(c_408, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_393, c_30])).
% 3.00/1.46  tff(c_415, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_408])).
% 3.00/1.46  tff(c_416, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_415])).
% 3.00/1.46  tff(c_420, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_128, c_416])).
% 3.00/1.46  tff(c_433, plain, (![D_122, C_123, B_124, A_125]: (m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(C_123, B_124))) | ~r1_tarski(k2_relat_1(D_122), B_124) | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(C_123, A_125))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.00/1.46  tff(c_444, plain, (![B_126]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_126))) | ~r1_tarski(k2_relat_1('#skF_5'), B_126))), inference(resolution, [status(thm)], [c_36, c_433])).
% 3.00/1.46  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.00/1.46  tff(c_499, plain, (![B_128]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', B_128)) | ~r1_tarski(k2_relat_1('#skF_5'), B_128))), inference(resolution, [status(thm)], [c_444, c_4])).
% 3.00/1.46  tff(c_503, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', '#skF_4')) | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_138, c_499])).
% 3.00/1.46  tff(c_522, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_179, c_503])).
% 3.00/1.46  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.00/1.46  tff(c_302, plain, (![A_90, B_91]: (r1_tarski(k1_relat_1(A_90), k1_relat_1(B_91)) | ~r1_tarski(A_90, B_91) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.46  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_10, B_11)), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.00/1.46  tff(c_126, plain, (![A_58, A_10, B_11]: (r1_tarski(A_58, A_10) | ~r1_tarski(A_58, k1_relat_1(k2_zfmisc_1(A_10, B_11))))), inference(resolution, [status(thm)], [c_14, c_113])).
% 3.00/1.46  tff(c_306, plain, (![A_90, A_10, B_11]: (r1_tarski(k1_relat_1(A_90), A_10) | ~r1_tarski(A_90, k2_zfmisc_1(A_10, B_11)) | ~v1_relat_1(k2_zfmisc_1(A_10, B_11)) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_302, c_126])).
% 3.00/1.46  tff(c_661, plain, (![A_139, A_140, B_141]: (r1_tarski(k1_relat_1(A_139), A_140) | ~r1_tarski(A_139, k2_zfmisc_1(A_140, B_141)) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_306])).
% 3.00/1.46  tff(c_667, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_522, c_661])).
% 3.00/1.46  tff(c_688, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_667])).
% 3.00/1.46  tff(c_690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_420, c_688])).
% 3.00/1.46  tff(c_691, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_415])).
% 3.00/1.46  tff(c_695, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_138, c_691])).
% 3.00/1.46  tff(c_702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_179, c_695])).
% 3.00/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  Inference rules
% 3.00/1.46  ----------------------
% 3.00/1.46  #Ref     : 0
% 3.00/1.46  #Sup     : 140
% 3.00/1.46  #Fact    : 0
% 3.00/1.46  #Define  : 0
% 3.00/1.46  #Split   : 6
% 3.00/1.46  #Chain   : 0
% 3.00/1.46  #Close   : 0
% 3.00/1.46  
% 3.00/1.46  Ordering : KBO
% 3.00/1.46  
% 3.00/1.46  Simplification rules
% 3.00/1.46  ----------------------
% 3.00/1.46  #Subsume      : 18
% 3.00/1.46  #Demod        : 33
% 3.00/1.46  #Tautology    : 18
% 3.00/1.46  #SimpNegUnit  : 2
% 3.00/1.46  #BackRed      : 0
% 3.00/1.46  
% 3.00/1.46  #Partial instantiations: 0
% 3.00/1.46  #Strategies tried      : 1
% 3.00/1.46  
% 3.00/1.46  Timing (in seconds)
% 3.00/1.46  ----------------------
% 3.00/1.47  Preprocessing        : 0.29
% 3.00/1.47  Parsing              : 0.17
% 3.00/1.47  CNF conversion       : 0.02
% 3.00/1.47  Main loop            : 0.37
% 3.00/1.47  Inferencing          : 0.15
% 3.00/1.47  Reduction            : 0.11
% 3.00/1.47  Demodulation         : 0.07
% 3.00/1.47  BG Simplification    : 0.02
% 3.00/1.47  Subsumption          : 0.07
% 3.00/1.47  Abstraction          : 0.01
% 3.00/1.47  MUC search           : 0.00
% 3.00/1.47  Cooper               : 0.00
% 3.00/1.47  Total                : 0.69
% 3.00/1.47  Index Insertion      : 0.00
% 3.00/1.47  Index Deletion       : 0.00
% 3.00/1.47  Index Matching       : 0.00
% 3.00/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
