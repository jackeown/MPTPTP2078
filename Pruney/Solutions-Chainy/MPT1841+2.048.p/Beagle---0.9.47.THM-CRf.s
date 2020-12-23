%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 131 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 262 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_141,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_150,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_141])).

tff(c_155,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_150])).

tff(c_207,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k6_domain_1(A_70,B_71),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_216,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_207])).

tff(c_220,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_216])).

tff(c_221,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_220])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_229,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_22])).

tff(c_30,plain,(
    ! [B_27,A_25] :
      ( B_27 = A_25
      | ~ r1_tarski(A_25,B_27)
      | ~ v1_zfmisc_1(B_27)
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_232,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_229,c_30])).

tff(c_241,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_232])).

tff(c_242,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_241])).

tff(c_281,plain,(
    v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_73,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),A_44)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_114,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_110,c_12])).

tff(c_286,plain,(
    ! [B_75] : k2_xboole_0(k1_tarski('#skF_5'),B_75) = B_75 ),
    inference(resolution,[status(thm)],[c_281,c_114])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),B_13) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_295,plain,(
    ! [B_75] : k1_xboole_0 != B_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_14])).

tff(c_310,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_295])).

tff(c_311,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_34,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_156,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_34])).

tff(c_316,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_156])).

tff(c_20,plain,(
    ! [A_17] : m1_subset_1('#skF_3'(A_17),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_49,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    ! [A_17] : r1_tarski('#skF_3'(A_17),A_17) ),
    inference(resolution,[status(thm)],[c_20,c_49])).

tff(c_189,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(A_68,B_67)
      | ~ v1_zfmisc_1(B_67)
      | v1_xboole_0(B_67)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_202,plain,(
    ! [A_17] :
      ( '#skF_3'(A_17) = A_17
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17)
      | v1_xboole_0('#skF_3'(A_17)) ) ),
    inference(resolution,[status(thm)],[c_57,c_189])).

tff(c_18,plain,(
    ! [A_17] : ~ v1_subset_1('#skF_3'(A_17),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_251,plain,(
    ! [B_72,A_73] :
      ( ~ v1_xboole_0(B_72)
      | v1_subset_1(B_72,A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_263,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_3'(A_17))
      | v1_subset_1('#skF_3'(A_17),A_17)
      | v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_20,c_251])).

tff(c_272,plain,(
    ! [A_74] :
      ( ~ v1_xboole_0('#skF_3'(A_74))
      | v1_xboole_0(A_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_263])).

tff(c_402,plain,(
    ! [A_80] :
      ( '#skF_3'(A_80) = A_80
      | ~ v1_zfmisc_1(A_80)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_202,c_272])).

tff(c_405,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_402])).

tff(c_408,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_405])).

tff(c_430,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_18])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  
% 2.32/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.32/1.31  
% 2.32/1.31  %Foreground sorts:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Background operators:
% 2.32/1.31  
% 2.32/1.31  
% 2.32/1.31  %Foreground operators:
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.32/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.32/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.32/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.31  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.32/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.32/1.31  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.32/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.31  
% 2.32/1.33  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.32/1.33  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.32/1.33  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.32/1.33  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.32/1.33  tff(f_94, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.32/1.33  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.32/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.32/1.33  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.32/1.33  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.32/1.33  tff(f_63, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.32/1.33  tff(f_57, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.32/1.33  tff(c_38, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.32/1.33  tff(c_32, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.32/1.33  tff(c_36, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.32/1.33  tff(c_141, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.32/1.33  tff(c_150, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_141])).
% 2.32/1.33  tff(c_155, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_150])).
% 2.32/1.33  tff(c_207, plain, (![A_70, B_71]: (m1_subset_1(k6_domain_1(A_70, B_71), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.33  tff(c_216, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_155, c_207])).
% 2.32/1.33  tff(c_220, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_216])).
% 2.32/1.33  tff(c_221, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_220])).
% 2.32/1.33  tff(c_22, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.32/1.33  tff(c_229, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_221, c_22])).
% 2.32/1.33  tff(c_30, plain, (![B_27, A_25]: (B_27=A_25 | ~r1_tarski(A_25, B_27) | ~v1_zfmisc_1(B_27) | v1_xboole_0(B_27) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.32/1.33  tff(c_232, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_229, c_30])).
% 2.32/1.33  tff(c_241, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_232])).
% 2.32/1.33  tff(c_242, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0(k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_38, c_241])).
% 2.32/1.33  tff(c_281, plain, (v1_xboole_0(k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_242])).
% 2.32/1.33  tff(c_73, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), A_44) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.32/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.33  tff(c_110, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.32/1.33  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.32/1.33  tff(c_114, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_110, c_12])).
% 2.32/1.33  tff(c_286, plain, (![B_75]: (k2_xboole_0(k1_tarski('#skF_5'), B_75)=B_75)), inference(resolution, [status(thm)], [c_281, c_114])).
% 2.32/1.33  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.32/1.33  tff(c_295, plain, (![B_75]: (k1_xboole_0!=B_75)), inference(superposition, [status(thm), theory('equality')], [c_286, c_14])).
% 2.32/1.33  tff(c_310, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_295])).
% 2.32/1.33  tff(c_311, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_242])).
% 2.32/1.33  tff(c_34, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.32/1.33  tff(c_156, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_34])).
% 2.32/1.33  tff(c_316, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_156])).
% 2.32/1.33  tff(c_20, plain, (![A_17]: (m1_subset_1('#skF_3'(A_17), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.32/1.33  tff(c_49, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.32/1.33  tff(c_57, plain, (![A_17]: (r1_tarski('#skF_3'(A_17), A_17))), inference(resolution, [status(thm)], [c_20, c_49])).
% 2.32/1.33  tff(c_189, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(A_68, B_67) | ~v1_zfmisc_1(B_67) | v1_xboole_0(B_67) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.32/1.33  tff(c_202, plain, (![A_17]: ('#skF_3'(A_17)=A_17 | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17) | v1_xboole_0('#skF_3'(A_17)))), inference(resolution, [status(thm)], [c_57, c_189])).
% 2.32/1.33  tff(c_18, plain, (![A_17]: (~v1_subset_1('#skF_3'(A_17), A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.32/1.33  tff(c_251, plain, (![B_72, A_73]: (~v1_xboole_0(B_72) | v1_subset_1(B_72, A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.32/1.33  tff(c_263, plain, (![A_17]: (~v1_xboole_0('#skF_3'(A_17)) | v1_subset_1('#skF_3'(A_17), A_17) | v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_20, c_251])).
% 2.32/1.33  tff(c_272, plain, (![A_74]: (~v1_xboole_0('#skF_3'(A_74)) | v1_xboole_0(A_74))), inference(negUnitSimplification, [status(thm)], [c_18, c_263])).
% 2.32/1.33  tff(c_402, plain, (![A_80]: ('#skF_3'(A_80)=A_80 | ~v1_zfmisc_1(A_80) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_202, c_272])).
% 2.32/1.33  tff(c_405, plain, ('#skF_3'('#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_402])).
% 2.32/1.33  tff(c_408, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38, c_405])).
% 2.32/1.33  tff(c_430, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_408, c_18])).
% 2.32/1.33  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_430])).
% 2.32/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  Inference rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Ref     : 1
% 2.32/1.33  #Sup     : 89
% 2.32/1.33  #Fact    : 0
% 2.32/1.33  #Define  : 0
% 2.32/1.33  #Split   : 2
% 2.32/1.33  #Chain   : 0
% 2.32/1.33  #Close   : 0
% 2.32/1.33  
% 2.32/1.33  Ordering : KBO
% 2.32/1.33  
% 2.32/1.33  Simplification rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Subsume      : 12
% 2.32/1.33  #Demod        : 25
% 2.32/1.33  #Tautology    : 45
% 2.32/1.33  #SimpNegUnit  : 11
% 2.32/1.33  #BackRed      : 6
% 2.32/1.33  
% 2.32/1.33  #Partial instantiations: 0
% 2.32/1.33  #Strategies tried      : 1
% 2.32/1.33  
% 2.32/1.33  Timing (in seconds)
% 2.32/1.33  ----------------------
% 2.32/1.33  Preprocessing        : 0.30
% 2.32/1.33  Parsing              : 0.16
% 2.32/1.33  CNF conversion       : 0.02
% 2.32/1.33  Main loop            : 0.23
% 2.32/1.33  Inferencing          : 0.10
% 2.32/1.33  Reduction            : 0.07
% 2.32/1.33  Demodulation         : 0.04
% 2.32/1.33  BG Simplification    : 0.01
% 2.32/1.33  Subsumption          : 0.04
% 2.32/1.33  Abstraction          : 0.01
% 2.32/1.33  MUC search           : 0.00
% 2.32/1.33  Cooper               : 0.00
% 2.32/1.34  Total                : 0.57
% 2.32/1.34  Index Insertion      : 0.00
% 2.32/1.34  Index Deletion       : 0.00
% 2.32/1.34  Index Matching       : 0.00
% 2.32/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
