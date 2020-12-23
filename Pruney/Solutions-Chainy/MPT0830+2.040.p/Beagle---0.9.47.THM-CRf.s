%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:31 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 113 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 189 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_38,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_44,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_35,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_41,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_43,plain,(
    ! [C_36,B_37,A_38] :
      ( v5_relat_1(C_36,B_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_17,A_16)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [A_96,A_97,B_98] :
      ( r1_tarski(A_96,A_97)
      | ~ r1_tarski(A_96,k2_relat_1(B_98))
      | ~ v5_relat_1(B_98,A_97)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_192,plain,(
    ! [B_17,A_16,A_97] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_17,A_16)),A_97)
      | ~ v5_relat_1(B_17,A_97)
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_20,c_183])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [C_39,A_40,B_41] :
      ( v4_relat_1(C_39,A_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_73,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(k7_relat_1(C_49,A_50))
      | ~ v4_relat_1(C_49,B_51)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    ! [A_50] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_50))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_78,plain,(
    ! [A_50] : v1_relat_1(k7_relat_1('#skF_4',A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_75])).

tff(c_235,plain,(
    ! [C_105,A_106,B_107] :
      ( m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ r1_tarski(k2_relat_1(C_105),B_107)
      | ~ r1_tarski(k1_relat_1(C_105),A_106)
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_140,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( k5_relset_1(A_77,B_78,C_79,D_80) = k7_relat_1(C_79,D_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,(
    ! [D_80] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_80) = k7_relat_1('#skF_4',D_80) ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_30,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_144,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_30])).

tff(c_238,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_235,c_144])).

tff(c_252,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_238])).

tff(c_259,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_262,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_259])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_262])).

tff(c_267,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_271,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_267])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_47,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.36  
% 2.36/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.36  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.36  
% 2.36/1.36  %Foreground sorts:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Background operators:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Foreground operators:
% 2.36/1.36  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.36/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.36/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.36/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.36  
% 2.51/1.38  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.51/1.38  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.51/1.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.51/1.38  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.51/1.38  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 2.51/1.38  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.51/1.38  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.51/1.38  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.51/1.38  tff(f_54, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.51/1.38  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.51/1.38  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.51/1.38  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.38  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.38  tff(c_35, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.38  tff(c_38, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_35])).
% 2.51/1.38  tff(c_41, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 2.51/1.38  tff(c_43, plain, (![C_36, B_37, A_38]: (v5_relat_1(C_36, B_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_37))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.38  tff(c_47, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_43])).
% 2.51/1.38  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(k7_relat_1(B_17, A_16)), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.38  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.38  tff(c_53, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.38  tff(c_183, plain, (![A_96, A_97, B_98]: (r1_tarski(A_96, A_97) | ~r1_tarski(A_96, k2_relat_1(B_98)) | ~v5_relat_1(B_98, A_97) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_8, c_53])).
% 2.51/1.38  tff(c_192, plain, (![B_17, A_16, A_97]: (r1_tarski(k2_relat_1(k7_relat_1(B_17, A_16)), A_97) | ~v5_relat_1(B_17, A_97) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_20, c_183])).
% 2.51/1.38  tff(c_18, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.51/1.38  tff(c_48, plain, (![C_39, A_40, B_41]: (v4_relat_1(C_39, A_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.51/1.38  tff(c_52, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.51/1.38  tff(c_73, plain, (![C_49, A_50, B_51]: (v1_relat_1(k7_relat_1(C_49, A_50)) | ~v4_relat_1(C_49, B_51) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.51/1.38  tff(c_75, plain, (![A_50]: (v1_relat_1(k7_relat_1('#skF_4', A_50)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_73])).
% 2.51/1.38  tff(c_78, plain, (![A_50]: (v1_relat_1(k7_relat_1('#skF_4', A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_75])).
% 2.51/1.38  tff(c_235, plain, (![C_105, A_106, B_107]: (m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~r1_tarski(k2_relat_1(C_105), B_107) | ~r1_tarski(k1_relat_1(C_105), A_106) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.51/1.38  tff(c_140, plain, (![A_77, B_78, C_79, D_80]: (k5_relset_1(A_77, B_78, C_79, D_80)=k7_relat_1(C_79, D_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.51/1.38  tff(c_143, plain, (![D_80]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_80)=k7_relat_1('#skF_4', D_80))), inference(resolution, [status(thm)], [c_32, c_140])).
% 2.51/1.38  tff(c_30, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.38  tff(c_144, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_30])).
% 2.51/1.38  tff(c_238, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_235, c_144])).
% 2.51/1.38  tff(c_252, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_238])).
% 2.51/1.38  tff(c_259, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_252])).
% 2.51/1.38  tff(c_262, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_259])).
% 2.51/1.38  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_262])).
% 2.51/1.38  tff(c_267, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_252])).
% 2.51/1.38  tff(c_271, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_267])).
% 2.51/1.38  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_47, c_271])).
% 2.51/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  Inference rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Ref     : 0
% 2.51/1.38  #Sup     : 48
% 2.51/1.38  #Fact    : 0
% 2.51/1.38  #Define  : 0
% 2.51/1.38  #Split   : 1
% 2.51/1.38  #Chain   : 0
% 2.51/1.38  #Close   : 0
% 2.51/1.38  
% 2.51/1.38  Ordering : KBO
% 2.51/1.38  
% 2.51/1.38  Simplification rules
% 2.51/1.38  ----------------------
% 2.51/1.38  #Subsume      : 1
% 2.51/1.38  #Demod        : 17
% 2.51/1.38  #Tautology    : 4
% 2.51/1.38  #SimpNegUnit  : 0
% 2.51/1.38  #BackRed      : 1
% 2.51/1.38  
% 2.51/1.38  #Partial instantiations: 0
% 2.51/1.38  #Strategies tried      : 1
% 2.51/1.38  
% 2.51/1.38  Timing (in seconds)
% 2.51/1.38  ----------------------
% 2.51/1.38  Preprocessing        : 0.33
% 2.51/1.38  Parsing              : 0.17
% 2.51/1.38  CNF conversion       : 0.02
% 2.51/1.38  Main loop            : 0.25
% 2.51/1.38  Inferencing          : 0.10
% 2.51/1.38  Reduction            : 0.08
% 2.51/1.38  Demodulation         : 0.06
% 2.51/1.38  BG Simplification    : 0.01
% 2.51/1.38  Subsumption          : 0.04
% 2.51/1.38  Abstraction          : 0.03
% 2.51/1.38  MUC search           : 0.00
% 2.51/1.38  Cooper               : 0.00
% 2.51/1.38  Total                : 0.62
% 2.51/1.38  Index Insertion      : 0.00
% 2.51/1.38  Index Deletion       : 0.00
% 2.51/1.38  Index Matching       : 0.00
% 2.51/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
