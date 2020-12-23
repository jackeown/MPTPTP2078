%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 131 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 311 expanded)
%              Number of equality atoms :   52 ( 139 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_32,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_77,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_85,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_91,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_100,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_91])).

tff(c_103,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_38,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_1'(A_15),A_15)
      | ~ v1_zfmisc_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_121,plain,(
    ! [A_36,B_37] :
      ( k6_domain_1(A_36,B_37) = k1_tarski(B_37)
      | ~ m1_subset_1(B_37,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,(
    ! [A_47] :
      ( k6_domain_1(A_47,'#skF_1'(A_47)) = k1_tarski('#skF_1'(A_47))
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_38,c_121])).

tff(c_36,plain,(
    ! [A_15] :
      ( k6_domain_1(A_15,'#skF_1'(A_15)) = A_15
      | ~ v1_zfmisc_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_167,plain,(
    ! [A_48] :
      ( k1_tarski('#skF_1'(A_48)) = A_48
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48)
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_36])).

tff(c_30,plain,(
    ! [B_11,A_10,C_12] :
      ( k1_xboole_0 = B_11
      | k1_tarski(A_10) = B_11
      | k2_xboole_0(B_11,C_12) != k1_tarski(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_233,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_tarski('#skF_1'(A_57)) = B_56
      | k2_xboole_0(B_56,C_58) != A_57
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_30])).

tff(c_235,plain,(
    ! [A_57] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski('#skF_1'(A_57)) = '#skF_3'
      | A_57 != '#skF_3'
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57)
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_233])).

tff(c_236,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_247,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_247])).

tff(c_260,plain,(
    ! [A_62] :
      ( k1_tarski('#skF_1'(A_62)) = '#skF_3'
      | A_62 != '#skF_3'
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_126,plain,(
    ! [A_38,C_39,B_40] :
      ( k1_tarski(A_38) = C_39
      | k1_xboole_0 = C_39
      | k2_xboole_0(B_40,C_39) != k1_tarski(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_129,plain,(
    ! [A_38] :
      ( k1_tarski(A_38) = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(A_38) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_126])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_137,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_2])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_137])).

tff(c_140,plain,(
    ! [A_38] :
      ( k1_tarski(A_38) = '#skF_2'
      | k1_tarski(A_38) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_176,plain,(
    ! [A_48] :
      ( k1_tarski('#skF_1'(A_48)) = '#skF_2'
      | A_48 != '#skF_3'
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48)
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_140])).

tff(c_266,plain,(
    ! [A_62] :
      ( '#skF_2' = '#skF_3'
      | A_62 != '#skF_3'
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | A_62 != '#skF_3'
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_176])).

tff(c_302,plain,(
    ! [A_66] :
      ( A_66 != '#skF_3'
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66)
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66)
      | A_66 != '#skF_3'
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66)
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_266])).

tff(c_304,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_302])).

tff(c_307,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_304])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:10:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.27/1.28  
% 2.27/1.28  %Foreground sorts:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Background operators:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Foreground operators:
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.27/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.28  
% 2.27/1.29  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.27/1.29  tff(f_32, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.27/1.29  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.27/1.29  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.27/1.29  tff(f_73, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.27/1.29  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.27/1.29  tff(f_56, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.27/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.27/1.29  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.29  tff(c_44, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.29  tff(c_40, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.29  tff(c_8, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.29  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.29  tff(c_77, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.27/1.29  tff(c_85, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_77])).
% 2.27/1.29  tff(c_91, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.29  tff(c_100, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_91])).
% 2.27/1.29  tff(c_103, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_100])).
% 2.27/1.29  tff(c_38, plain, (![A_15]: (m1_subset_1('#skF_1'(A_15), A_15) | ~v1_zfmisc_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.27/1.29  tff(c_121, plain, (![A_36, B_37]: (k6_domain_1(A_36, B_37)=k1_tarski(B_37) | ~m1_subset_1(B_37, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.29  tff(c_152, plain, (![A_47]: (k6_domain_1(A_47, '#skF_1'(A_47))=k1_tarski('#skF_1'(A_47)) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_38, c_121])).
% 2.27/1.29  tff(c_36, plain, (![A_15]: (k6_domain_1(A_15, '#skF_1'(A_15))=A_15 | ~v1_zfmisc_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.27/1.29  tff(c_167, plain, (![A_48]: (k1_tarski('#skF_1'(A_48))=A_48 | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48) | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(superposition, [status(thm), theory('equality')], [c_152, c_36])).
% 2.27/1.29  tff(c_30, plain, (![B_11, A_10, C_12]: (k1_xboole_0=B_11 | k1_tarski(A_10)=B_11 | k2_xboole_0(B_11, C_12)!=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.29  tff(c_233, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_tarski('#skF_1'(A_57))=B_56 | k2_xboole_0(B_56, C_58)!=A_57 | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_167, c_30])).
% 2.27/1.29  tff(c_235, plain, (![A_57]: (k1_xboole_0='#skF_3' | k1_tarski('#skF_1'(A_57))='#skF_3' | A_57!='#skF_3' | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_103, c_233])).
% 2.27/1.29  tff(c_236, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_235])).
% 2.27/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.27/1.29  tff(c_247, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_2])).
% 2.27/1.29  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_247])).
% 2.27/1.29  tff(c_260, plain, (![A_62]: (k1_tarski('#skF_1'(A_62))='#skF_3' | A_62!='#skF_3' | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(splitRight, [status(thm)], [c_235])).
% 2.27/1.29  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.29  tff(c_126, plain, (![A_38, C_39, B_40]: (k1_tarski(A_38)=C_39 | k1_xboole_0=C_39 | k2_xboole_0(B_40, C_39)!=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.29  tff(c_129, plain, (![A_38]: (k1_tarski(A_38)='#skF_2' | k1_xboole_0='#skF_2' | k1_tarski(A_38)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_103, c_126])).
% 2.27/1.29  tff(c_130, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_129])).
% 2.27/1.29  tff(c_137, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_2])).
% 2.27/1.29  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_137])).
% 2.27/1.29  tff(c_140, plain, (![A_38]: (k1_tarski(A_38)='#skF_2' | k1_tarski(A_38)!='#skF_3')), inference(splitRight, [status(thm)], [c_129])).
% 2.27/1.29  tff(c_176, plain, (![A_48]: (k1_tarski('#skF_1'(A_48))='#skF_2' | A_48!='#skF_3' | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48) | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(superposition, [status(thm), theory('equality')], [c_167, c_140])).
% 2.27/1.29  tff(c_266, plain, (![A_62]: ('#skF_2'='#skF_3' | A_62!='#skF_3' | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | A_62!='#skF_3' | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_260, c_176])).
% 2.27/1.29  tff(c_302, plain, (![A_66]: (A_66!='#skF_3' | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66) | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66) | A_66!='#skF_3' | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66) | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66))), inference(negUnitSimplification, [status(thm)], [c_40, c_266])).
% 2.27/1.29  tff(c_304, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_302])).
% 2.27/1.29  tff(c_307, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_304])).
% 2.27/1.29  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_307])).
% 2.27/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  Inference rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Ref     : 3
% 2.27/1.29  #Sup     : 56
% 2.27/1.29  #Fact    : 0
% 2.27/1.29  #Define  : 0
% 2.27/1.29  #Split   : 2
% 2.27/1.29  #Chain   : 0
% 2.27/1.29  #Close   : 0
% 2.27/1.29  
% 2.27/1.29  Ordering : KBO
% 2.27/1.29  
% 2.27/1.29  Simplification rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Subsume      : 14
% 2.27/1.29  #Demod        : 20
% 2.27/1.29  #Tautology    : 27
% 2.27/1.29  #SimpNegUnit  : 8
% 2.27/1.29  #BackRed      : 18
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.29  Timing (in seconds)
% 2.27/1.29  ----------------------
% 2.27/1.30  Preprocessing        : 0.30
% 2.27/1.30  Parsing              : 0.16
% 2.27/1.30  CNF conversion       : 0.02
% 2.27/1.30  Main loop            : 0.24
% 2.27/1.30  Inferencing          : 0.08
% 2.27/1.30  Reduction            : 0.06
% 2.27/1.30  Demodulation         : 0.04
% 2.27/1.30  BG Simplification    : 0.02
% 2.27/1.30  Subsumption          : 0.06
% 2.27/1.30  Abstraction          : 0.01
% 2.27/1.30  MUC search           : 0.00
% 2.27/1.30  Cooper               : 0.00
% 2.27/1.30  Total                : 0.58
% 2.27/1.30  Index Insertion      : 0.00
% 2.27/1.30  Index Deletion       : 0.00
% 2.27/1.30  Index Matching       : 0.00
% 2.27/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
