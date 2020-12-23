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
% DateTime   : Thu Dec  3 10:28:33 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 141 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 ( 275 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [A_40,B_41] : k2_xboole_0(k1_tarski(A_40),B_41) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [A_40] : k1_tarski(A_40) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_64])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_196,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_208,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_196])).

tff(c_214,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_208])).

tff(c_380,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k6_domain_1(A_94,B_95),k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_391,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_380])).

tff(c_396,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_391])).

tff(c_397,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_396])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_408,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_397,c_32])).

tff(c_42,plain,(
    ! [B_34,A_32] :
      ( B_34 = A_32
      | ~ r1_tarski(A_32,B_34)
      | ~ v1_zfmisc_1(B_34)
      | v1_xboole_0(B_34)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_414,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_408,c_42])).

tff(c_423,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_414])).

tff(c_424,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_423])).

tff(c_444,plain,(
    v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_103,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_2'(A_57,B_58),A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_115,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_85,c_115])).

tff(c_148,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_113,c_131])).

tff(c_452,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_444,c_148])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_452])).

tff(c_459,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_46,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_215,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_46])).

tff(c_463,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_215])).

tff(c_30,plain,(
    ! [A_21] : m1_subset_1('#skF_3'(A_21),k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    ! [A_21] : r1_tarski('#skF_3'(A_21),A_21) ),
    inference(resolution,[status(thm)],[c_30,c_77])).

tff(c_284,plain,(
    ! [B_82,A_83] :
      ( B_82 = A_83
      | ~ r1_tarski(A_83,B_82)
      | ~ v1_zfmisc_1(B_82)
      | v1_xboole_0(B_82)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2444,plain,(
    ! [A_176] :
      ( '#skF_3'(A_176) = A_176
      | ~ v1_zfmisc_1(A_176)
      | v1_xboole_0(A_176)
      | v1_xboole_0('#skF_3'(A_176)) ) ),
    inference(resolution,[status(thm)],[c_84,c_284])).

tff(c_28,plain,(
    ! [A_21] : ~ v1_subset_1('#skF_3'(A_21),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_475,plain,(
    ! [B_97,A_98] :
      ( ~ v1_xboole_0(B_97)
      | v1_subset_1(B_97,A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_488,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0('#skF_3'(A_21))
      | v1_subset_1('#skF_3'(A_21),A_21)
      | v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_30,c_475])).

tff(c_497,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0('#skF_3'(A_21))
      | v1_xboole_0(A_21) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_488])).

tff(c_2487,plain,(
    ! [A_177] :
      ( '#skF_3'(A_177) = A_177
      | ~ v1_zfmisc_1(A_177)
      | v1_xboole_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_2444,c_497])).

tff(c_2490,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2487])).

tff(c_2493,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2490])).

tff(c_2554,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2493,c_28])).

tff(c_2581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_2554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.79  
% 4.23/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.79  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 4.23/1.79  
% 4.23/1.79  %Foreground sorts:
% 4.23/1.79  
% 4.23/1.79  
% 4.23/1.79  %Background operators:
% 4.23/1.79  
% 4.23/1.79  
% 4.23/1.79  %Foreground operators:
% 4.23/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.79  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.23/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.23/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.23/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.79  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.23/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.23/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.23/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.23/1.79  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.23/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.23/1.79  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.23/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.23/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.23/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.23/1.79  
% 4.23/1.80  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.23/1.80  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.23/1.80  tff(f_120, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 4.23/1.80  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.23/1.80  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.23/1.80  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.23/1.80  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 4.23/1.80  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.23/1.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.23/1.80  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.23/1.80  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.23/1.80  tff(f_71, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 4.23/1.80  tff(f_65, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 4.23/1.80  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.23/1.80  tff(c_64, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.23/1.80  tff(c_68, plain, (![A_40]: (k1_tarski(A_40)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_64])).
% 4.23/1.80  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.23/1.80  tff(c_44, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.23/1.80  tff(c_48, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.23/1.80  tff(c_196, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.23/1.80  tff(c_208, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_196])).
% 4.23/1.80  tff(c_214, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_208])).
% 4.23/1.80  tff(c_380, plain, (![A_94, B_95]: (m1_subset_1(k6_domain_1(A_94, B_95), k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.23/1.80  tff(c_391, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_214, c_380])).
% 4.23/1.80  tff(c_396, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_391])).
% 4.23/1.80  tff(c_397, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_396])).
% 4.23/1.80  tff(c_32, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.23/1.80  tff(c_408, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_397, c_32])).
% 4.23/1.80  tff(c_42, plain, (![B_34, A_32]: (B_34=A_32 | ~r1_tarski(A_32, B_34) | ~v1_zfmisc_1(B_34) | v1_xboole_0(B_34) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.23/1.80  tff(c_414, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_408, c_42])).
% 4.23/1.80  tff(c_423, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_414])).
% 4.23/1.80  tff(c_424, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0(k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_423])).
% 4.23/1.80  tff(c_444, plain, (v1_xboole_0(k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_424])).
% 4.23/1.80  tff(c_103, plain, (![A_57, B_58]: (r2_hidden('#skF_2'(A_57, B_58), A_57) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.23/1.80  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.23/1.80  tff(c_113, plain, (![A_57, B_58]: (~v1_xboole_0(A_57) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_103, c_2])).
% 4.23/1.80  tff(c_24, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.23/1.80  tff(c_77, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.23/1.80  tff(c_85, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_24, c_77])).
% 4.23/1.80  tff(c_115, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.23/1.80  tff(c_131, plain, (![A_63]: (k1_xboole_0=A_63 | ~r1_tarski(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_85, c_115])).
% 4.23/1.80  tff(c_148, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_113, c_131])).
% 4.23/1.80  tff(c_452, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_444, c_148])).
% 4.23/1.80  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_452])).
% 4.23/1.80  tff(c_459, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_424])).
% 4.23/1.80  tff(c_46, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.23/1.80  tff(c_215, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_46])).
% 4.23/1.80  tff(c_463, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_215])).
% 4.23/1.80  tff(c_30, plain, (![A_21]: (m1_subset_1('#skF_3'(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.23/1.80  tff(c_84, plain, (![A_21]: (r1_tarski('#skF_3'(A_21), A_21))), inference(resolution, [status(thm)], [c_30, c_77])).
% 4.23/1.80  tff(c_284, plain, (![B_82, A_83]: (B_82=A_83 | ~r1_tarski(A_83, B_82) | ~v1_zfmisc_1(B_82) | v1_xboole_0(B_82) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.23/1.80  tff(c_2444, plain, (![A_176]: ('#skF_3'(A_176)=A_176 | ~v1_zfmisc_1(A_176) | v1_xboole_0(A_176) | v1_xboole_0('#skF_3'(A_176)))), inference(resolution, [status(thm)], [c_84, c_284])).
% 4.23/1.80  tff(c_28, plain, (![A_21]: (~v1_subset_1('#skF_3'(A_21), A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.23/1.80  tff(c_475, plain, (![B_97, A_98]: (~v1_xboole_0(B_97) | v1_subset_1(B_97, A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.23/1.80  tff(c_488, plain, (![A_21]: (~v1_xboole_0('#skF_3'(A_21)) | v1_subset_1('#skF_3'(A_21), A_21) | v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_30, c_475])).
% 4.23/1.80  tff(c_497, plain, (![A_21]: (~v1_xboole_0('#skF_3'(A_21)) | v1_xboole_0(A_21))), inference(negUnitSimplification, [status(thm)], [c_28, c_488])).
% 4.23/1.80  tff(c_2487, plain, (![A_177]: ('#skF_3'(A_177)=A_177 | ~v1_zfmisc_1(A_177) | v1_xboole_0(A_177))), inference(resolution, [status(thm)], [c_2444, c_497])).
% 4.23/1.80  tff(c_2490, plain, ('#skF_3'('#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2487])).
% 4.23/1.80  tff(c_2493, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_2490])).
% 4.23/1.80  tff(c_2554, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2493, c_28])).
% 4.23/1.80  tff(c_2581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_463, c_2554])).
% 4.23/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.80  
% 4.23/1.80  Inference rules
% 4.23/1.80  ----------------------
% 4.23/1.80  #Ref     : 0
% 4.23/1.80  #Sup     : 582
% 4.23/1.80  #Fact    : 0
% 4.23/1.80  #Define  : 0
% 4.23/1.80  #Split   : 7
% 4.23/1.80  #Chain   : 0
% 4.23/1.80  #Close   : 0
% 4.23/1.80  
% 4.23/1.80  Ordering : KBO
% 4.23/1.80  
% 4.23/1.80  Simplification rules
% 4.23/1.80  ----------------------
% 4.23/1.80  #Subsume      : 127
% 4.23/1.80  #Demod        : 276
% 4.23/1.80  #Tautology    : 179
% 4.23/1.80  #SimpNegUnit  : 60
% 4.23/1.80  #BackRed      : 12
% 4.23/1.80  
% 4.23/1.80  #Partial instantiations: 0
% 4.23/1.80  #Strategies tried      : 1
% 4.23/1.80  
% 4.23/1.80  Timing (in seconds)
% 4.23/1.80  ----------------------
% 4.23/1.81  Preprocessing        : 0.33
% 4.23/1.81  Parsing              : 0.18
% 4.23/1.81  CNF conversion       : 0.02
% 4.23/1.81  Main loop            : 0.65
% 4.23/1.81  Inferencing          : 0.22
% 4.23/1.81  Reduction            : 0.20
% 4.23/1.81  Demodulation         : 0.13
% 4.23/1.81  BG Simplification    : 0.03
% 4.23/1.81  Subsumption          : 0.16
% 4.23/1.81  Abstraction          : 0.03
% 4.23/1.81  MUC search           : 0.00
% 4.23/1.81  Cooper               : 0.00
% 4.23/1.81  Total                : 1.01
% 4.23/1.81  Index Insertion      : 0.00
% 4.23/1.81  Index Deletion       : 0.00
% 4.23/1.81  Index Matching       : 0.00
% 4.23/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
