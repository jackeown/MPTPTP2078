%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:18 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   62 (  90 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 186 expanded)
%              Number of equality atoms :   40 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_2'(A_20),A_20)
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_157,plain,(
    ! [A_45,B_46] :
      ( k6_domain_1(A_45,B_46) = k1_tarski(B_46)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_224,plain,(
    ! [A_62] :
      ( k6_domain_1(A_62,'#skF_2'(A_62)) = k1_tarski('#skF_2'(A_62))
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_42,c_157])).

tff(c_40,plain,(
    ! [A_20] :
      ( k6_domain_1(A_20,'#skF_2'(A_20)) = A_20
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_239,plain,(
    ! [A_63] :
      ( k1_tarski('#skF_2'(A_63)) = A_63
      | ~ v1_zfmisc_1(A_63)
      | v1_xboole_0(A_63)
      | ~ v1_zfmisc_1(A_63)
      | v1_xboole_0(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_40])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_86,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_86])).

tff(c_126,plain,(
    ! [A_41,B_42] : k2_xboole_0(A_41,k4_xboole_0(B_42,A_41)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_135,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_126])).

tff(c_141,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_135])).

tff(c_162,plain,(
    ! [A_47,C_48,B_49] :
      ( k1_tarski(A_47) = C_48
      | k1_xboole_0 = C_48
      | k2_xboole_0(B_49,C_48) != k1_tarski(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_165,plain,(
    ! [A_47] :
      ( k1_tarski(A_47) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k1_tarski(A_47) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_162])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [B_30,A_31] :
      ( ~ r1_tarski(B_30,A_31)
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [A_32] :
      ( ~ r1_tarski(A_32,'#skF_1'(A_32))
      | v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_74])).

tff(c_191,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_79])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_191])).

tff(c_196,plain,(
    ! [A_47] :
      ( k1_tarski(A_47) = '#skF_3'
      | k1_tarski(A_47) != '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_283,plain,(
    ! [A_70] :
      ( k1_tarski('#skF_2'(A_70)) = '#skF_3'
      | A_70 != '#skF_4'
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70)
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_196])).

tff(c_230,plain,(
    ! [A_62] :
      ( k1_tarski('#skF_2'(A_62)) = A_62
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_40])).

tff(c_328,plain,(
    ! [A_74] :
      ( A_74 = '#skF_3'
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | A_74 != '#skF_4'
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_230])).

tff(c_330,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_328])).

tff(c_333,plain,
    ( '#skF_3' = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_330])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:02:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.30  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.05/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.05/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.05/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.30  
% 2.42/1.31  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.42/1.31  tff(f_83, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.42/1.31  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.42/1.31  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.42/1.31  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.42/1.31  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.42/1.31  tff(f_61, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.42/1.31  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.42/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.42/1.31  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.42/1.31  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.42/1.31  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.42/1.31  tff(c_48, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.42/1.31  tff(c_42, plain, (![A_20]: (m1_subset_1('#skF_2'(A_20), A_20) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.31  tff(c_157, plain, (![A_45, B_46]: (k6_domain_1(A_45, B_46)=k1_tarski(B_46) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.42/1.31  tff(c_224, plain, (![A_62]: (k6_domain_1(A_62, '#skF_2'(A_62))=k1_tarski('#skF_2'(A_62)) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_42, c_157])).
% 2.42/1.31  tff(c_40, plain, (![A_20]: (k6_domain_1(A_20, '#skF_2'(A_20))=A_20 | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.31  tff(c_239, plain, (![A_63]: (k1_tarski('#skF_2'(A_63))=A_63 | ~v1_zfmisc_1(A_63) | v1_xboole_0(A_63) | ~v1_zfmisc_1(A_63) | v1_xboole_0(A_63))), inference(superposition, [status(thm), theory('equality')], [c_224, c_40])).
% 2.42/1.31  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.42/1.31  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.31  tff(c_46, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.42/1.31  tff(c_86, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.31  tff(c_98, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_86])).
% 2.42/1.31  tff(c_126, plain, (![A_41, B_42]: (k2_xboole_0(A_41, k4_xboole_0(B_42, A_41))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.31  tff(c_135, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98, c_126])).
% 2.42/1.31  tff(c_141, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_135])).
% 2.42/1.31  tff(c_162, plain, (![A_47, C_48, B_49]: (k1_tarski(A_47)=C_48 | k1_xboole_0=C_48 | k2_xboole_0(B_49, C_48)!=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.42/1.31  tff(c_165, plain, (![A_47]: (k1_tarski(A_47)='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski(A_47)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_141, c_162])).
% 2.42/1.31  tff(c_173, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_165])).
% 2.42/1.31  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.31  tff(c_69, plain, (![B_30, A_31]: (~r1_tarski(B_30, A_31) | ~r2_hidden(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.42/1.31  tff(c_74, plain, (![A_32]: (~r1_tarski(A_32, '#skF_1'(A_32)) | v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_4, c_69])).
% 2.42/1.31  tff(c_79, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_74])).
% 2.42/1.31  tff(c_191, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_79])).
% 2.42/1.31  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_191])).
% 2.42/1.31  tff(c_196, plain, (![A_47]: (k1_tarski(A_47)='#skF_3' | k1_tarski(A_47)!='#skF_4')), inference(splitRight, [status(thm)], [c_165])).
% 2.42/1.31  tff(c_283, plain, (![A_70]: (k1_tarski('#skF_2'(A_70))='#skF_3' | A_70!='#skF_4' | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70) | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_239, c_196])).
% 2.42/1.31  tff(c_230, plain, (![A_62]: (k1_tarski('#skF_2'(A_62))=A_62 | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_224, c_40])).
% 2.42/1.31  tff(c_328, plain, (![A_74]: (A_74='#skF_3' | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | A_74!='#skF_4' | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74))), inference(superposition, [status(thm), theory('equality')], [c_283, c_230])).
% 2.42/1.31  tff(c_330, plain, ('#skF_3'='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_328])).
% 2.42/1.31  tff(c_333, plain, ('#skF_3'='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_330])).
% 2.42/1.31  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_333])).
% 2.42/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.31  
% 2.42/1.31  Inference rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Ref     : 0
% 2.42/1.31  #Sup     : 72
% 2.42/1.31  #Fact    : 0
% 2.42/1.31  #Define  : 0
% 2.42/1.31  #Split   : 1
% 2.42/1.31  #Chain   : 0
% 2.42/1.31  #Close   : 0
% 2.42/1.31  
% 2.42/1.31  Ordering : KBO
% 2.42/1.31  
% 2.42/1.31  Simplification rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Subsume      : 10
% 2.42/1.31  #Demod        : 26
% 2.42/1.31  #Tautology    : 37
% 2.42/1.31  #SimpNegUnit  : 2
% 2.42/1.31  #BackRed      : 10
% 2.42/1.31  
% 2.42/1.31  #Partial instantiations: 0
% 2.42/1.31  #Strategies tried      : 1
% 2.42/1.31  
% 2.42/1.31  Timing (in seconds)
% 2.42/1.31  ----------------------
% 2.42/1.31  Preprocessing        : 0.31
% 2.42/1.31  Parsing              : 0.16
% 2.42/1.31  CNF conversion       : 0.02
% 2.42/1.31  Main loop            : 0.24
% 2.42/1.31  Inferencing          : 0.08
% 2.42/1.31  Reduction            : 0.06
% 2.42/1.31  Demodulation         : 0.04
% 2.42/1.31  BG Simplification    : 0.02
% 2.42/1.31  Subsumption          : 0.05
% 2.42/1.31  Abstraction          : 0.01
% 2.42/1.31  MUC search           : 0.00
% 2.42/1.31  Cooper               : 0.00
% 2.42/1.31  Total                : 0.57
% 2.42/1.31  Index Insertion      : 0.00
% 2.42/1.31  Index Deletion       : 0.00
% 2.42/1.31  Index Matching       : 0.00
% 2.42/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
