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
% DateTime   : Thu Dec  3 10:07:06 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   66 (  98 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 146 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_74,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_80])).

tff(c_204,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_213,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_204])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_333,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_342,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_333])).

tff(c_464,plain,(
    ! [A_121,B_122,C_123] :
      ( m1_subset_1(k1_relset_1(A_121,B_122,C_123),k1_zfmisc_1(A_121))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_485,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_464])).

tff(c_492,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_485])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_500,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_492,c_14])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [A_59,A_7,B_8] :
      ( r1_tarski(A_59,k2_xboole_0(A_7,B_8))
      | ~ r1_tarski(A_59,A_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_24,plain,(
    ! [A_23] :
      ( k2_xboole_0(k1_relat_1(A_23),k2_relat_1(A_23)) = k3_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_255,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(k2_xboole_0(A_87,C_88),B_89)
      | ~ r1_tarski(C_88,B_89)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1194,plain,(
    ! [A_237,B_238] :
      ( r1_tarski(k3_relat_1(A_237),B_238)
      | ~ r1_tarski(k2_relat_1(A_237),B_238)
      | ~ r1_tarski(k1_relat_1(A_237),B_238)
      | ~ v1_relat_1(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_255])).

tff(c_36,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1258,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1194,c_36])).

tff(c_1283,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1258])).

tff(c_1291,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1283])).

tff(c_1300,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_137,c_1291])).

tff(c_1309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_1300])).

tff(c_1310,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_1325,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1310])).

tff(c_1328,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1325])).

tff(c_1332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_213,c_1328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.62  
% 3.67/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.62  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.67/1.62  
% 3.67/1.62  %Foreground sorts:
% 3.67/1.62  
% 3.67/1.62  
% 3.67/1.62  %Background operators:
% 3.67/1.62  
% 3.67/1.62  
% 3.67/1.62  %Foreground operators:
% 3.67/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.62  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.67/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.67/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.67/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.67/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.67/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.67/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.67/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.67/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.67/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.67/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.67/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.67/1.62  
% 3.67/1.63  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.67/1.63  tff(f_89, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 3.67/1.63  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.67/1.63  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.67/1.63  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.67/1.63  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.67/1.63  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.67/1.63  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.67/1.63  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.67/1.63  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.67/1.63  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.67/1.63  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.67/1.63  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.67/1.63  tff(c_26, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.67/1.63  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.67/1.63  tff(c_74, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.67/1.63  tff(c_80, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 3.67/1.63  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_80])).
% 3.67/1.63  tff(c_204, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.67/1.63  tff(c_213, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_204])).
% 3.67/1.63  tff(c_22, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.67/1.63  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.67/1.63  tff(c_333, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.67/1.63  tff(c_342, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_333])).
% 3.67/1.63  tff(c_464, plain, (![A_121, B_122, C_123]: (m1_subset_1(k1_relset_1(A_121, B_122, C_123), k1_zfmisc_1(A_121)) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.67/1.63  tff(c_485, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_342, c_464])).
% 3.67/1.63  tff(c_492, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_485])).
% 3.67/1.63  tff(c_14, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.67/1.63  tff(c_500, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_492, c_14])).
% 3.67/1.63  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.67/1.63  tff(c_125, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.67/1.63  tff(c_137, plain, (![A_59, A_7, B_8]: (r1_tarski(A_59, k2_xboole_0(A_7, B_8)) | ~r1_tarski(A_59, A_7))), inference(resolution, [status(thm)], [c_6, c_125])).
% 3.67/1.63  tff(c_24, plain, (![A_23]: (k2_xboole_0(k1_relat_1(A_23), k2_relat_1(A_23))=k3_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.67/1.63  tff(c_255, plain, (![A_87, C_88, B_89]: (r1_tarski(k2_xboole_0(A_87, C_88), B_89) | ~r1_tarski(C_88, B_89) | ~r1_tarski(A_87, B_89))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.67/1.63  tff(c_1194, plain, (![A_237, B_238]: (r1_tarski(k3_relat_1(A_237), B_238) | ~r1_tarski(k2_relat_1(A_237), B_238) | ~r1_tarski(k1_relat_1(A_237), B_238) | ~v1_relat_1(A_237))), inference(superposition, [status(thm), theory('equality')], [c_24, c_255])).
% 3.67/1.63  tff(c_36, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.67/1.63  tff(c_1258, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1194, c_36])).
% 3.67/1.63  tff(c_1283, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1258])).
% 3.67/1.63  tff(c_1291, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1283])).
% 3.67/1.63  tff(c_1300, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_137, c_1291])).
% 3.67/1.63  tff(c_1309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_500, c_1300])).
% 3.67/1.63  tff(c_1310, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_1283])).
% 3.67/1.63  tff(c_1325, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_1310])).
% 3.67/1.63  tff(c_1328, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_1325])).
% 3.67/1.63  tff(c_1332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_213, c_1328])).
% 3.67/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.63  
% 3.67/1.63  Inference rules
% 3.67/1.63  ----------------------
% 3.67/1.63  #Ref     : 0
% 3.67/1.63  #Sup     : 311
% 3.67/1.63  #Fact    : 0
% 3.67/1.63  #Define  : 0
% 3.67/1.63  #Split   : 8
% 3.67/1.63  #Chain   : 0
% 3.67/1.63  #Close   : 0
% 3.67/1.63  
% 3.67/1.63  Ordering : KBO
% 3.67/1.63  
% 3.67/1.63  Simplification rules
% 3.67/1.63  ----------------------
% 3.67/1.63  #Subsume      : 48
% 3.67/1.63  #Demod        : 31
% 3.67/1.63  #Tautology    : 24
% 3.67/1.63  #SimpNegUnit  : 0
% 3.67/1.63  #BackRed      : 0
% 3.67/1.63  
% 3.67/1.63  #Partial instantiations: 0
% 3.67/1.63  #Strategies tried      : 1
% 3.67/1.63  
% 3.67/1.63  Timing (in seconds)
% 3.67/1.63  ----------------------
% 3.67/1.64  Preprocessing        : 0.32
% 3.67/1.64  Parsing              : 0.18
% 3.67/1.64  CNF conversion       : 0.02
% 3.67/1.64  Main loop            : 0.51
% 3.67/1.64  Inferencing          : 0.19
% 3.67/1.64  Reduction            : 0.14
% 3.67/1.64  Demodulation         : 0.10
% 3.67/1.64  BG Simplification    : 0.02
% 3.67/1.64  Subsumption          : 0.12
% 3.67/1.64  Abstraction          : 0.02
% 3.67/1.64  MUC search           : 0.00
% 3.67/1.64  Cooper               : 0.00
% 3.67/1.64  Total                : 0.87
% 3.67/1.64  Index Insertion      : 0.00
% 3.67/1.64  Index Deletion       : 0.00
% 3.67/1.64  Index Matching       : 0.00
% 3.67/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
