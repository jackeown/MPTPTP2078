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
% DateTime   : Thu Dec  3 10:07:30 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 115 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 187 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_50])).

tff(c_60,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_73,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_82,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_129,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(k7_relat_1(C_62,A_63))
      | ~ v4_relat_1(C_62,B_64)
      | ~ v1_relat_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [A_63] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_63))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_129])).

tff(c_134,plain,(
    ! [A_63] : v1_relat_1(k7_relat_1('#skF_4',A_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_131])).

tff(c_176,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(k7_relat_1(C_72,A_73),A_73)
      | ~ v4_relat_1(C_72,B_74)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_178,plain,(
    ! [A_73] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_73),A_73)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_176])).

tff(c_181,plain,(
    ! [A_73] : v4_relat_1(k7_relat_1('#skF_4',A_73),A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_178])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_17,A_16)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_300,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_relset_1(A_105,B_106,C_107) = k2_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_309,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_300])).

tff(c_387,plain,(
    ! [A_128,B_129,C_130] :
      ( m1_subset_1(k2_relset_1(A_128,B_129,C_130),k1_zfmisc_1(B_129))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_408,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_387])).

tff(c_415,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_408])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_423,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_415,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_436,plain,(
    ! [A_131] :
      ( r1_tarski(A_131,'#skF_3')
      | ~ r1_tarski(A_131,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_423,c_2])).

tff(c_444,plain,(
    ! [A_16] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_16)),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_436])).

tff(c_448,plain,(
    ! [A_16] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_16)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_444])).

tff(c_591,plain,(
    ! [C_144,A_145,B_146] :
      ( m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ r1_tarski(k2_relat_1(C_144),B_146)
      | ~ r1_tarski(k1_relat_1(C_144),A_145)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_460,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k5_relset_1(A_133,B_134,C_135,D_136) = k7_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_471,plain,(
    ! [D_136] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_136) = k7_relat_1('#skF_4',D_136) ),
    inference(resolution,[status(thm)],[c_38,c_460])).

tff(c_36,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_473,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_36])).

tff(c_594,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_591,c_473])).

tff(c_614,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_448,c_594])).

tff(c_625,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_614])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_181,c_625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.45  
% 2.69/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.46  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.69/1.46  
% 2.69/1.46  %Foreground sorts:
% 2.69/1.46  
% 2.69/1.46  
% 2.69/1.46  %Background operators:
% 2.69/1.46  
% 2.69/1.46  
% 2.69/1.46  %Foreground operators:
% 2.69/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.69/1.46  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.69/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.69/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.46  
% 3.10/1.47  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.10/1.47  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 3.10/1.47  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.10/1.47  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.47  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 3.10/1.47  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.10/1.47  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 3.10/1.47  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.10/1.47  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.10/1.47  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.10/1.47  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.10/1.47  tff(f_90, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.10/1.47  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.10/1.47  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.10/1.47  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.10/1.47  tff(c_50, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.47  tff(c_56, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_50])).
% 3.10/1.47  tff(c_60, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56])).
% 3.10/1.47  tff(c_73, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.47  tff(c_82, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_73])).
% 3.10/1.47  tff(c_129, plain, (![C_62, A_63, B_64]: (v1_relat_1(k7_relat_1(C_62, A_63)) | ~v4_relat_1(C_62, B_64) | ~v1_relat_1(C_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.10/1.47  tff(c_131, plain, (![A_63]: (v1_relat_1(k7_relat_1('#skF_4', A_63)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_82, c_129])).
% 3.10/1.47  tff(c_134, plain, (![A_63]: (v1_relat_1(k7_relat_1('#skF_4', A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_131])).
% 3.10/1.47  tff(c_176, plain, (![C_72, A_73, B_74]: (v4_relat_1(k7_relat_1(C_72, A_73), A_73) | ~v4_relat_1(C_72, B_74) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.10/1.47  tff(c_178, plain, (![A_73]: (v4_relat_1(k7_relat_1('#skF_4', A_73), A_73) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_82, c_176])).
% 3.10/1.47  tff(c_181, plain, (![A_73]: (v4_relat_1(k7_relat_1('#skF_4', A_73), A_73))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_178])).
% 3.10/1.47  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.10/1.47  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(k7_relat_1(B_17, A_16)), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.10/1.47  tff(c_300, plain, (![A_105, B_106, C_107]: (k2_relset_1(A_105, B_106, C_107)=k2_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.10/1.47  tff(c_309, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_300])).
% 3.10/1.47  tff(c_387, plain, (![A_128, B_129, C_130]: (m1_subset_1(k2_relset_1(A_128, B_129, C_130), k1_zfmisc_1(B_129)) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.10/1.47  tff(c_408, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_309, c_387])).
% 3.10/1.47  tff(c_415, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_408])).
% 3.10/1.47  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.10/1.47  tff(c_423, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_415, c_4])).
% 3.10/1.47  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.47  tff(c_436, plain, (![A_131]: (r1_tarski(A_131, '#skF_3') | ~r1_tarski(A_131, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_423, c_2])).
% 3.10/1.47  tff(c_444, plain, (![A_16]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_16)), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_436])).
% 3.10/1.47  tff(c_448, plain, (![A_16]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_16)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_444])).
% 3.10/1.47  tff(c_591, plain, (![C_144, A_145, B_146]: (m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~r1_tarski(k2_relat_1(C_144), B_146) | ~r1_tarski(k1_relat_1(C_144), A_145) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.10/1.47  tff(c_460, plain, (![A_133, B_134, C_135, D_136]: (k5_relset_1(A_133, B_134, C_135, D_136)=k7_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.10/1.47  tff(c_471, plain, (![D_136]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_136)=k7_relat_1('#skF_4', D_136))), inference(resolution, [status(thm)], [c_38, c_460])).
% 3.10/1.47  tff(c_36, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.10/1.47  tff(c_473, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_36])).
% 3.10/1.47  tff(c_594, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_591, c_473])).
% 3.10/1.47  tff(c_614, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_448, c_594])).
% 3.10/1.47  tff(c_625, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_614])).
% 3.10/1.47  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_181, c_625])).
% 3.10/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.47  
% 3.10/1.47  Inference rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Ref     : 0
% 3.10/1.47  #Sup     : 124
% 3.10/1.47  #Fact    : 0
% 3.10/1.47  #Define  : 0
% 3.10/1.47  #Split   : 3
% 3.10/1.47  #Chain   : 0
% 3.10/1.47  #Close   : 0
% 3.10/1.47  
% 3.10/1.47  Ordering : KBO
% 3.10/1.47  
% 3.10/1.47  Simplification rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Subsume      : 15
% 3.10/1.47  #Demod        : 43
% 3.10/1.47  #Tautology    : 16
% 3.10/1.47  #SimpNegUnit  : 0
% 3.10/1.47  #BackRed      : 2
% 3.10/1.47  
% 3.10/1.47  #Partial instantiations: 0
% 3.10/1.47  #Strategies tried      : 1
% 3.10/1.47  
% 3.10/1.47  Timing (in seconds)
% 3.10/1.47  ----------------------
% 3.10/1.48  Preprocessing        : 0.33
% 3.10/1.48  Parsing              : 0.18
% 3.10/1.48  CNF conversion       : 0.02
% 3.10/1.48  Main loop            : 0.37
% 3.10/1.48  Inferencing          : 0.14
% 3.10/1.48  Reduction            : 0.11
% 3.10/1.48  Demodulation         : 0.08
% 3.10/1.48  BG Simplification    : 0.02
% 3.10/1.48  Subsumption          : 0.07
% 3.10/1.48  Abstraction          : 0.02
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.73
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
