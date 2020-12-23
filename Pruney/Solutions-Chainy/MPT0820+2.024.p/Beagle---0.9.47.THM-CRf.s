%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:03 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 180 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_18,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_149,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_152,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_152])).

tff(c_178,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_182,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_178])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_193,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_189])).

tff(c_20,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_196,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_193,c_20])).

tff(c_199,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_196])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_21)),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_203,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_22])).

tff(c_207,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_203])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [B_34,A_35] : k3_tarski(k2_tarski(B_34,A_35)) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_65])).

tff(c_8,plain,(
    ! [A_9,B_10] : k3_tarski(k2_tarski(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_8])).

tff(c_137,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,k2_xboole_0(C_39,B_40))
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [A_38,B_34,A_35] :
      ( r1_tarski(A_38,k2_xboole_0(B_34,A_35))
      | ~ r1_tarski(A_38,B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_137])).

tff(c_16,plain,(
    ! [A_16] :
      ( k2_xboole_0(k1_relat_1(A_16),k2_relat_1(A_16)) = k3_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_236,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(k2_xboole_0(A_63,C_64),B_65)
      | ~ r1_tarski(C_64,B_65)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_272,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k3_relat_1(A_74),B_75)
      | ~ r1_tarski(k2_relat_1(A_74),B_75)
      | ~ r1_tarski(k1_relat_1(A_74),B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_236])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_281,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_272,c_28])).

tff(c_290,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_281])).

tff(c_298,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_301,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_143,c_298])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_301])).

tff(c_309,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_324,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_309])).

tff(c_327,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_324])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_182,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.27  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.27  
% 2.11/1.27  %Foreground sorts:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Background operators:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Foreground operators:
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.11/1.27  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.11/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.11/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.11/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.27  
% 2.11/1.28  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.11/1.28  tff(f_79, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 2.11/1.28  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.11/1.28  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.11/1.28  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.11/1.28  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.11/1.28  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.11/1.28  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.11/1.28  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.11/1.28  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.11/1.28  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.11/1.28  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.11/1.28  tff(c_18, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.28  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.28  tff(c_149, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.28  tff(c_152, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_149])).
% 2.11/1.28  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_152])).
% 2.11/1.28  tff(c_178, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.11/1.28  tff(c_182, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_178])).
% 2.11/1.28  tff(c_14, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.28  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.28  tff(c_189, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.11/1.28  tff(c_193, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_189])).
% 2.11/1.28  tff(c_20, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.28  tff(c_196, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_193, c_20])).
% 2.11/1.28  tff(c_199, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_196])).
% 2.11/1.28  tff(c_22, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_21)), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.28  tff(c_203, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_199, c_22])).
% 2.11/1.28  tff(c_207, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_203])).
% 2.11/1.28  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.28  tff(c_65, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.28  tff(c_81, plain, (![B_34, A_35]: (k3_tarski(k2_tarski(B_34, A_35))=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_65])).
% 2.11/1.28  tff(c_8, plain, (![A_9, B_10]: (k3_tarski(k2_tarski(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.28  tff(c_87, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_81, c_8])).
% 2.11/1.28  tff(c_137, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, k2_xboole_0(C_39, B_40)) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.28  tff(c_143, plain, (![A_38, B_34, A_35]: (r1_tarski(A_38, k2_xboole_0(B_34, A_35)) | ~r1_tarski(A_38, B_34))), inference(superposition, [status(thm), theory('equality')], [c_87, c_137])).
% 2.11/1.28  tff(c_16, plain, (![A_16]: (k2_xboole_0(k1_relat_1(A_16), k2_relat_1(A_16))=k3_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.28  tff(c_236, plain, (![A_63, C_64, B_65]: (r1_tarski(k2_xboole_0(A_63, C_64), B_65) | ~r1_tarski(C_64, B_65) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.28  tff(c_272, plain, (![A_74, B_75]: (r1_tarski(k3_relat_1(A_74), B_75) | ~r1_tarski(k2_relat_1(A_74), B_75) | ~r1_tarski(k1_relat_1(A_74), B_75) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_16, c_236])).
% 2.11/1.28  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.28  tff(c_281, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_272, c_28])).
% 2.11/1.28  tff(c_290, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_281])).
% 2.11/1.28  tff(c_298, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_290])).
% 2.11/1.28  tff(c_301, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_143, c_298])).
% 2.11/1.28  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_301])).
% 2.11/1.28  tff(c_309, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_290])).
% 2.11/1.28  tff(c_324, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_309])).
% 2.11/1.28  tff(c_327, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_324])).
% 2.11/1.28  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_182, c_327])).
% 2.11/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.28  
% 2.11/1.28  Inference rules
% 2.11/1.28  ----------------------
% 2.11/1.28  #Ref     : 0
% 2.11/1.28  #Sup     : 68
% 2.11/1.28  #Fact    : 0
% 2.11/1.28  #Define  : 0
% 2.11/1.28  #Split   : 2
% 2.11/1.28  #Chain   : 0
% 2.11/1.28  #Close   : 0
% 2.11/1.28  
% 2.11/1.28  Ordering : KBO
% 2.11/1.28  
% 2.11/1.28  Simplification rules
% 2.11/1.28  ----------------------
% 2.11/1.28  #Subsume      : 12
% 2.11/1.28  #Demod        : 15
% 2.11/1.28  #Tautology    : 28
% 2.11/1.28  #SimpNegUnit  : 0
% 2.11/1.28  #BackRed      : 0
% 2.11/1.28  
% 2.11/1.28  #Partial instantiations: 0
% 2.11/1.28  #Strategies tried      : 1
% 2.11/1.28  
% 2.11/1.28  Timing (in seconds)
% 2.11/1.28  ----------------------
% 2.11/1.29  Preprocessing        : 0.29
% 2.11/1.29  Parsing              : 0.17
% 2.11/1.29  CNF conversion       : 0.02
% 2.11/1.29  Main loop            : 0.23
% 2.11/1.29  Inferencing          : 0.09
% 2.11/1.29  Reduction            : 0.08
% 2.11/1.29  Demodulation         : 0.06
% 2.11/1.29  BG Simplification    : 0.01
% 2.11/1.29  Subsumption          : 0.04
% 2.11/1.29  Abstraction          : 0.01
% 2.11/1.29  MUC search           : 0.00
% 2.11/1.29  Cooper               : 0.00
% 2.11/1.29  Total                : 0.55
% 2.11/1.29  Index Insertion      : 0.00
% 2.11/1.29  Index Deletion       : 0.00
% 2.11/1.29  Index Matching       : 0.00
% 2.11/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
