%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:16 EST 2020

% Result     : Theorem 21.15s
% Output     : CNFRefutation 21.25s
% Verified   : 
% Statistics : Number of formulae       :   65 (  91 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 159 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_108,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_66,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_66,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    ! [A_41] :
      ( k6_domain_1(A_41,'#skF_4'(A_41)) = A_41
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    ! [A_41] :
      ( m1_subset_1('#skF_4'(A_41),A_41)
      | ~ v1_zfmisc_1(A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1804,plain,(
    ! [A_142,B_143] :
      ( k6_domain_1(A_142,B_143) = k1_tarski(B_143)
      | ~ m1_subset_1(B_143,A_142)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8495,plain,(
    ! [A_367] :
      ( k6_domain_1(A_367,'#skF_4'(A_367)) = k1_tarski('#skF_4'(A_367))
      | ~ v1_zfmisc_1(A_367)
      | v1_xboole_0(A_367) ) ),
    inference(resolution,[status(thm)],[c_60,c_1804])).

tff(c_40248,plain,(
    ! [A_838] :
      ( k1_tarski('#skF_4'(A_838)) = A_838
      | ~ v1_zfmisc_1(A_838)
      | v1_xboole_0(A_838)
      | ~ v1_zfmisc_1(A_838)
      | v1_xboole_0(A_838) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_8495])).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    ! [A_25] : k4_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_523,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(A_82,k2_xboole_0(C_83,B_84))
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_553,plain,(
    ! [A_85,A_86] :
      ( r1_tarski(A_85,A_86)
      | ~ r1_tarski(A_85,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_523])).

tff(c_556,plain,(
    ! [A_13,A_86] :
      ( r1_tarski(A_13,A_86)
      | k4_xboole_0(A_13,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_553])).

tff(c_571,plain,(
    ! [A_87,A_88] :
      ( r1_tarski(A_87,A_88)
      | k1_xboole_0 != A_87 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_556])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [B_60,A_61] :
      ( ~ r1_tarski(B_60,A_61)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_191,plain,(
    ! [A_3] :
      ( ~ r1_tarski(A_3,'#skF_1'(A_3))
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_591,plain,(
    ! [A_89] :
      ( v1_xboole_0(A_89)
      | k1_xboole_0 != A_89 ) ),
    inference(resolution,[status(thm)],[c_571,c_191])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_599,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_591,c_70])).

tff(c_598,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_591,c_68])).

tff(c_64,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_238,plain,(
    ! [A_63,B_64] :
      ( k2_xboole_0(A_63,B_64) = B_64
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_255,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_64,c_238])).

tff(c_2230,plain,(
    ! [C_166,B_167,A_168] :
      ( k1_xboole_0 = C_166
      | k1_xboole_0 = B_167
      | C_166 = B_167
      | k2_xboole_0(B_167,C_166) != k1_tarski(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2254,plain,(
    ! [A_168] :
      ( k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | '#skF_5' = '#skF_6'
      | k1_tarski(A_168) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_2230])).

tff(c_2263,plain,(
    ! [A_168] : k1_tarski(A_168) != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_599,c_598,c_2254])).

tff(c_77135,plain,(
    ! [A_1350] :
      ( A_1350 != '#skF_6'
      | ~ v1_zfmisc_1(A_1350)
      | v1_xboole_0(A_1350)
      | ~ v1_zfmisc_1(A_1350)
      | v1_xboole_0(A_1350) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40248,c_2263])).

tff(c_77137,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_77135])).

tff(c_77140,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_77137])).

tff(c_77142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_77140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.15/12.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.15/12.42  
% 21.15/12.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.15/12.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 21.15/12.42  
% 21.15/12.42  %Foreground sorts:
% 21.15/12.42  
% 21.15/12.42  
% 21.15/12.42  %Background operators:
% 21.15/12.42  
% 21.15/12.42  
% 21.15/12.42  %Foreground operators:
% 21.15/12.42  tff('#skF_4', type, '#skF_4': $i > $i).
% 21.15/12.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.15/12.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.15/12.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.15/12.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.15/12.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 21.15/12.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.15/12.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 21.15/12.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.15/12.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.15/12.42  tff('#skF_5', type, '#skF_5': $i).
% 21.15/12.42  tff('#skF_6', type, '#skF_6': $i).
% 21.15/12.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 21.15/12.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.15/12.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 21.15/12.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.15/12.42  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 21.15/12.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.15/12.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.15/12.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.15/12.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.15/12.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.15/12.42  
% 21.25/12.43  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 21.25/12.43  tff(f_108, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 21.25/12.43  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 21.25/12.43  tff(f_66, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 21.25/12.43  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 21.25/12.43  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 21.25/12.43  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 21.25/12.43  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 21.25/12.43  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 21.25/12.43  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 21.25/12.43  tff(f_84, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 21.25/12.43  tff(c_68, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 21.25/12.43  tff(c_66, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 21.25/12.43  tff(c_58, plain, (![A_41]: (k6_domain_1(A_41, '#skF_4'(A_41))=A_41 | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.25/12.43  tff(c_60, plain, (![A_41]: (m1_subset_1('#skF_4'(A_41), A_41) | ~v1_zfmisc_1(A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_108])).
% 21.25/12.43  tff(c_1804, plain, (![A_142, B_143]: (k6_domain_1(A_142, B_143)=k1_tarski(B_143) | ~m1_subset_1(B_143, A_142) | v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_98])).
% 21.25/12.43  tff(c_8495, plain, (![A_367]: (k6_domain_1(A_367, '#skF_4'(A_367))=k1_tarski('#skF_4'(A_367)) | ~v1_zfmisc_1(A_367) | v1_xboole_0(A_367))), inference(resolution, [status(thm)], [c_60, c_1804])).
% 21.25/12.43  tff(c_40248, plain, (![A_838]: (k1_tarski('#skF_4'(A_838))=A_838 | ~v1_zfmisc_1(A_838) | v1_xboole_0(A_838) | ~v1_zfmisc_1(A_838) | v1_xboole_0(A_838))), inference(superposition, [status(thm), theory('equality')], [c_58, c_8495])).
% 21.25/12.43  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 21.25/12.43  tff(c_40, plain, (![A_25]: (k4_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_66])).
% 21.25/12.43  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.25/12.43  tff(c_34, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.25/12.43  tff(c_523, plain, (![A_82, C_83, B_84]: (r1_tarski(A_82, k2_xboole_0(C_83, B_84)) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_50])).
% 21.25/12.43  tff(c_553, plain, (![A_85, A_86]: (r1_tarski(A_85, A_86) | ~r1_tarski(A_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_523])).
% 21.25/12.43  tff(c_556, plain, (![A_13, A_86]: (r1_tarski(A_13, A_86) | k4_xboole_0(A_13, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_553])).
% 21.25/12.43  tff(c_571, plain, (![A_87, A_88]: (r1_tarski(A_87, A_88) | k1_xboole_0!=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_556])).
% 21.25/12.43  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.25/12.43  tff(c_187, plain, (![B_60, A_61]: (~r1_tarski(B_60, A_61) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_91])).
% 21.25/12.43  tff(c_191, plain, (![A_3]: (~r1_tarski(A_3, '#skF_1'(A_3)) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_187])).
% 21.25/12.43  tff(c_591, plain, (![A_89]: (v1_xboole_0(A_89) | k1_xboole_0!=A_89)), inference(resolution, [status(thm)], [c_571, c_191])).
% 21.25/12.43  tff(c_70, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 21.25/12.43  tff(c_599, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_591, c_70])).
% 21.25/12.43  tff(c_598, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_591, c_68])).
% 21.25/12.43  tff(c_64, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 21.25/12.43  tff(c_238, plain, (![A_63, B_64]: (k2_xboole_0(A_63, B_64)=B_64 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.25/12.43  tff(c_255, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_64, c_238])).
% 21.25/12.43  tff(c_2230, plain, (![C_166, B_167, A_168]: (k1_xboole_0=C_166 | k1_xboole_0=B_167 | C_166=B_167 | k2_xboole_0(B_167, C_166)!=k1_tarski(A_168))), inference(cnfTransformation, [status(thm)], [f_84])).
% 21.25/12.43  tff(c_2254, plain, (![A_168]: (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | '#skF_5'='#skF_6' | k1_tarski(A_168)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_255, c_2230])).
% 21.25/12.43  tff(c_2263, plain, (![A_168]: (k1_tarski(A_168)!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_62, c_599, c_598, c_2254])).
% 21.25/12.43  tff(c_77135, plain, (![A_1350]: (A_1350!='#skF_6' | ~v1_zfmisc_1(A_1350) | v1_xboole_0(A_1350) | ~v1_zfmisc_1(A_1350) | v1_xboole_0(A_1350))), inference(superposition, [status(thm), theory('equality')], [c_40248, c_2263])).
% 21.25/12.43  tff(c_77137, plain, (~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_77135])).
% 21.25/12.43  tff(c_77140, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_77137])).
% 21.25/12.43  tff(c_77142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_77140])).
% 21.25/12.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.25/12.43  
% 21.25/12.43  Inference rules
% 21.25/12.43  ----------------------
% 21.25/12.43  #Ref     : 4
% 21.25/12.43  #Sup     : 20633
% 21.25/12.43  #Fact    : 0
% 21.25/12.43  #Define  : 0
% 21.25/12.43  #Split   : 5
% 21.25/12.43  #Chain   : 0
% 21.25/12.43  #Close   : 0
% 21.25/12.43  
% 21.25/12.43  Ordering : KBO
% 21.25/12.43  
% 21.25/12.43  Simplification rules
% 21.25/12.43  ----------------------
% 21.25/12.43  #Subsume      : 10839
% 21.25/12.43  #Demod        : 6934
% 21.25/12.43  #Tautology    : 3695
% 21.25/12.43  #SimpNegUnit  : 754
% 21.25/12.43  #BackRed      : 23
% 21.25/12.43  
% 21.25/12.43  #Partial instantiations: 0
% 21.25/12.43  #Strategies tried      : 1
% 21.25/12.43  
% 21.25/12.43  Timing (in seconds)
% 21.25/12.43  ----------------------
% 21.25/12.43  Preprocessing        : 0.33
% 21.25/12.43  Parsing              : 0.17
% 21.25/12.43  CNF conversion       : 0.02
% 21.25/12.43  Main loop            : 11.35
% 21.25/12.43  Inferencing          : 1.48
% 21.25/12.43  Reduction            : 5.29
% 21.25/12.43  Demodulation         : 4.14
% 21.25/12.43  BG Simplification    : 0.15
% 21.25/12.44  Subsumption          : 3.82
% 21.25/12.44  Abstraction          : 0.23
% 21.25/12.44  MUC search           : 0.00
% 21.25/12.44  Cooper               : 0.00
% 21.25/12.44  Total                : 11.70
% 21.25/12.44  Index Insertion      : 0.00
% 21.25/12.44  Index Deletion       : 0.00
% 21.25/12.44  Index Matching       : 0.00
% 21.25/12.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
