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
% DateTime   : Thu Dec  3 10:07:35 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :   62 (  71 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 104 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_453,plain,(
    ! [A_106,B_107,D_108] :
      ( r2_relset_1(A_106,B_107,D_108,D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_460,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_453])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_113,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_113])).

tff(c_123,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_119])).

tff(c_100,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_108,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_100])).

tff(c_257,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(k2_zfmisc_1(A_69,C_70),k2_zfmisc_1(B_71,C_70))
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_774,plain,(
    ! [A_165,C_166,B_167] :
      ( k2_xboole_0(k2_zfmisc_1(A_165,C_166),k2_zfmisc_1(B_167,C_166)) = k2_zfmisc_1(B_167,C_166)
      | ~ r1_tarski(A_165,B_167) ) ),
    inference(resolution,[status(thm)],[c_257,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,k2_xboole_0(C_44,B_45))
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [A_43,B_2,A_1] :
      ( r1_tarski(A_43,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_43,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_4641,plain,(
    ! [A_329,B_330,C_331,A_332] :
      ( r1_tarski(A_329,k2_zfmisc_1(B_330,C_331))
      | ~ r1_tarski(A_329,k2_zfmisc_1(A_332,C_331))
      | ~ r1_tarski(A_332,B_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_136])).

tff(c_4654,plain,(
    ! [B_333] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_333,'#skF_1'))
      | ~ r1_tarski('#skF_2',B_333) ) ),
    inference(resolution,[status(thm)],[c_108,c_4641])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_202,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_210,plain,(
    ! [A_11,A_57,B_58] :
      ( v4_relat_1(A_11,A_57)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_57,B_58)) ) ),
    inference(resolution,[status(thm)],[c_14,c_202])).

tff(c_4753,plain,(
    ! [B_334] :
      ( v4_relat_1('#skF_4',B_334)
      | ~ r1_tarski('#skF_2',B_334) ) ),
    inference(resolution,[status(thm)],[c_4654,c_210])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4756,plain,(
    ! [B_334] :
      ( k7_relat_1('#skF_4',B_334) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_334) ) ),
    inference(resolution,[status(thm)],[c_4753,c_20])).

tff(c_4760,plain,(
    ! [B_335] :
      ( k7_relat_1('#skF_4',B_335) = '#skF_4'
      | ~ r1_tarski('#skF_2',B_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_4756])).

tff(c_4795,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_4760])).

tff(c_549,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k5_relset_1(A_120,B_121,C_122,D_123) = k7_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_556,plain,(
    ! [D_123] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_123) = k7_relat_1('#skF_4',D_123) ),
    inference(resolution,[status(thm)],[c_36,c_549])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_557,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_32])).

tff(c_4796,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4795,c_557])).

tff(c_4799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_4796])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.32  
% 6.10/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.32  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.10/2.32  
% 6.10/2.32  %Foreground sorts:
% 6.10/2.32  
% 6.10/2.32  
% 6.10/2.32  %Background operators:
% 6.10/2.32  
% 6.10/2.32  
% 6.10/2.32  %Foreground operators:
% 6.10/2.32  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 6.10/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.10/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.10/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.32  tff('#skF_2', type, '#skF_2': $i).
% 6.10/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.10/2.32  tff('#skF_1', type, '#skF_1': $i).
% 6.10/2.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.10/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.10/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.10/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.10/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.10/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.10/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.10/2.32  
% 6.10/2.35  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 6.10/2.35  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.10/2.35  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.10/2.35  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.10/2.35  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.10/2.35  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 6.10/2.35  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.10/2.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.10/2.35  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.10/2.35  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.10/2.35  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.10/2.35  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 6.10/2.35  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.10/2.35  tff(c_453, plain, (![A_106, B_107, D_108]: (r2_relset_1(A_106, B_107, D_108, D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.10/2.35  tff(c_460, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_453])).
% 6.10/2.35  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.10/2.35  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.10/2.35  tff(c_113, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.10/2.35  tff(c_119, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_113])).
% 6.10/2.35  tff(c_123, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_119])).
% 6.10/2.35  tff(c_100, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.10/2.35  tff(c_108, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_100])).
% 6.10/2.35  tff(c_257, plain, (![A_69, C_70, B_71]: (r1_tarski(k2_zfmisc_1(A_69, C_70), k2_zfmisc_1(B_71, C_70)) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.10/2.35  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.10/2.35  tff(c_774, plain, (![A_165, C_166, B_167]: (k2_xboole_0(k2_zfmisc_1(A_165, C_166), k2_zfmisc_1(B_167, C_166))=k2_zfmisc_1(B_167, C_166) | ~r1_tarski(A_165, B_167))), inference(resolution, [status(thm)], [c_257, c_6])).
% 6.10/2.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.10/2.35  tff(c_124, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, k2_xboole_0(C_44, B_45)) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.10/2.35  tff(c_136, plain, (![A_43, B_2, A_1]: (r1_tarski(A_43, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_43, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 6.10/2.35  tff(c_4641, plain, (![A_329, B_330, C_331, A_332]: (r1_tarski(A_329, k2_zfmisc_1(B_330, C_331)) | ~r1_tarski(A_329, k2_zfmisc_1(A_332, C_331)) | ~r1_tarski(A_332, B_330))), inference(superposition, [status(thm), theory('equality')], [c_774, c_136])).
% 6.10/2.35  tff(c_4654, plain, (![B_333]: (r1_tarski('#skF_4', k2_zfmisc_1(B_333, '#skF_1')) | ~r1_tarski('#skF_2', B_333))), inference(resolution, [status(thm)], [c_108, c_4641])).
% 6.10/2.35  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.10/2.35  tff(c_202, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.10/2.35  tff(c_210, plain, (![A_11, A_57, B_58]: (v4_relat_1(A_11, A_57) | ~r1_tarski(A_11, k2_zfmisc_1(A_57, B_58)))), inference(resolution, [status(thm)], [c_14, c_202])).
% 6.10/2.35  tff(c_4753, plain, (![B_334]: (v4_relat_1('#skF_4', B_334) | ~r1_tarski('#skF_2', B_334))), inference(resolution, [status(thm)], [c_4654, c_210])).
% 6.10/2.35  tff(c_20, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.10/2.35  tff(c_4756, plain, (![B_334]: (k7_relat_1('#skF_4', B_334)='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_334))), inference(resolution, [status(thm)], [c_4753, c_20])).
% 6.10/2.35  tff(c_4760, plain, (![B_335]: (k7_relat_1('#skF_4', B_335)='#skF_4' | ~r1_tarski('#skF_2', B_335))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_4756])).
% 6.10/2.35  tff(c_4795, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_4760])).
% 6.10/2.35  tff(c_549, plain, (![A_120, B_121, C_122, D_123]: (k5_relset_1(A_120, B_121, C_122, D_123)=k7_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.10/2.35  tff(c_556, plain, (![D_123]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_123)=k7_relat_1('#skF_4', D_123))), inference(resolution, [status(thm)], [c_36, c_549])).
% 6.10/2.35  tff(c_32, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.10/2.35  tff(c_557, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_32])).
% 6.10/2.35  tff(c_4796, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4795, c_557])).
% 6.10/2.35  tff(c_4799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_460, c_4796])).
% 6.10/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.35  
% 6.10/2.35  Inference rules
% 6.10/2.35  ----------------------
% 6.10/2.35  #Ref     : 0
% 6.10/2.35  #Sup     : 1324
% 6.10/2.35  #Fact    : 0
% 6.10/2.35  #Define  : 0
% 6.10/2.35  #Split   : 7
% 6.10/2.35  #Chain   : 0
% 6.10/2.35  #Close   : 0
% 6.10/2.35  
% 6.10/2.35  Ordering : KBO
% 6.10/2.35  
% 6.10/2.35  Simplification rules
% 6.10/2.35  ----------------------
% 6.10/2.35  #Subsume      : 420
% 6.10/2.35  #Demod        : 278
% 6.10/2.35  #Tautology    : 283
% 6.10/2.35  #SimpNegUnit  : 0
% 6.10/2.35  #BackRed      : 2
% 6.10/2.35  
% 6.10/2.35  #Partial instantiations: 0
% 6.10/2.35  #Strategies tried      : 1
% 6.10/2.35  
% 6.10/2.35  Timing (in seconds)
% 6.10/2.35  ----------------------
% 6.35/2.35  Preprocessing        : 0.31
% 6.35/2.35  Parsing              : 0.16
% 6.35/2.35  CNF conversion       : 0.02
% 6.35/2.35  Main loop            : 1.15
% 6.36/2.35  Inferencing          : 0.35
% 6.36/2.36  Reduction            : 0.39
% 6.36/2.36  Demodulation         : 0.30
% 6.36/2.36  BG Simplification    : 0.04
% 6.36/2.36  Subsumption          : 0.28
% 6.36/2.36  Abstraction          : 0.05
% 6.36/2.36  MUC search           : 0.00
% 6.36/2.36  Cooper               : 0.00
% 6.36/2.36  Total                : 1.51
% 6.36/2.36  Index Insertion      : 0.00
% 6.36/2.36  Index Deletion       : 0.00
% 6.36/2.36  Index Matching       : 0.00
% 6.36/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
