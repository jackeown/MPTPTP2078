%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:20 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 175 expanded)
%              Number of equality atoms :   45 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_1'(A_15),A_15)
      | ~ v1_zfmisc_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [A_37,B_38] :
      ( k6_domain_1(A_37,B_38) = k1_tarski(B_38)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_151,plain,(
    ! [A_53] :
      ( k6_domain_1(A_53,'#skF_1'(A_53)) = k1_tarski('#skF_1'(A_53))
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_38,c_121])).

tff(c_36,plain,(
    ! [A_15] :
      ( k6_domain_1(A_15,'#skF_1'(A_15)) = A_15
      | ~ v1_zfmisc_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_166,plain,(
    ! [A_54] :
      ( k1_tarski('#skF_1'(A_54)) = A_54
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54)
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_36])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_65,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_65])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [B_29,A_30] :
      ( ~ r1_xboole_0(B_29,A_30)
      | ~ r1_tarski(B_29,A_30)
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_35,B_36] :
      ( ~ r1_tarski(A_35,B_36)
      | v1_xboole_0(A_35)
      | k4_xboole_0(A_35,B_36) != A_35 ) ),
    inference(resolution,[status(thm)],[c_12,c_78])).

tff(c_116,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_110])).

tff(c_119,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_116])).

tff(c_120,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_119])).

tff(c_6,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_83])).

tff(c_95,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_130,plain,(
    ! [A_42,C_43,B_44] :
      ( k1_tarski(A_42) = C_43
      | k1_xboole_0 = C_43
      | k2_xboole_0(B_44,C_43) != k1_tarski(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_133,plain,(
    ! [A_42] :
      ( k1_tarski(A_42) = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(A_42) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_130])).

tff(c_134,plain,(
    ! [A_42] :
      ( k1_tarski(A_42) = '#skF_2'
      | k1_tarski(A_42) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_133])).

tff(c_188,plain,(
    ! [A_55] :
      ( k1_tarski('#skF_1'(A_55)) = '#skF_2'
      | A_55 != '#skF_3'
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55)
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_134])).

tff(c_157,plain,(
    ! [A_53] :
      ( k1_tarski('#skF_1'(A_53)) = A_53
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53)
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_36])).

tff(c_283,plain,(
    ! [A_71] :
      ( A_71 = '#skF_2'
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | A_71 != '#skF_3'
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71)
      | ~ v1_zfmisc_1(A_71)
      | v1_xboole_0(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_157])).

tff(c_285,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_283])).

tff(c_288,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_285])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  
% 2.28/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.28/1.33  
% 2.28/1.33  %Foreground sorts:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Background operators:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Foreground operators:
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.28/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.28/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.33  
% 2.28/1.34  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.28/1.34  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.28/1.34  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.28/1.34  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.28/1.34  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.28/1.34  tff(f_39, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.28/1.34  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.28/1.34  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.28/1.34  tff(f_63, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.28/1.34  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.28/1.34  tff(c_40, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.28/1.34  tff(c_44, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.28/1.34  tff(c_38, plain, (![A_15]: (m1_subset_1('#skF_1'(A_15), A_15) | ~v1_zfmisc_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.28/1.34  tff(c_121, plain, (![A_37, B_38]: (k6_domain_1(A_37, B_38)=k1_tarski(B_38) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.28/1.34  tff(c_151, plain, (![A_53]: (k6_domain_1(A_53, '#skF_1'(A_53))=k1_tarski('#skF_1'(A_53)) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_38, c_121])).
% 2.28/1.34  tff(c_36, plain, (![A_15]: (k6_domain_1(A_15, '#skF_1'(A_15))=A_15 | ~v1_zfmisc_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.28/1.34  tff(c_166, plain, (![A_54]: (k1_tarski('#skF_1'(A_54))=A_54 | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(superposition, [status(thm), theory('equality')], [c_151, c_36])).
% 2.28/1.34  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.28/1.34  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.28/1.34  tff(c_65, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.34  tff(c_73, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_65])).
% 2.28/1.34  tff(c_12, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k4_xboole_0(A_6, B_7)!=A_6)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.34  tff(c_78, plain, (![B_29, A_30]: (~r1_xboole_0(B_29, A_30) | ~r1_tarski(B_29, A_30) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.34  tff(c_110, plain, (![A_35, B_36]: (~r1_tarski(A_35, B_36) | v1_xboole_0(A_35) | k4_xboole_0(A_35, B_36)!=A_35)), inference(resolution, [status(thm)], [c_12, c_78])).
% 2.28/1.34  tff(c_116, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_42, c_110])).
% 2.28/1.34  tff(c_119, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_116])).
% 2.28/1.34  tff(c_120, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_119])).
% 2.28/1.34  tff(c_6, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.34  tff(c_83, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.34  tff(c_92, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73, c_83])).
% 2.28/1.34  tff(c_95, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92])).
% 2.28/1.34  tff(c_130, plain, (![A_42, C_43, B_44]: (k1_tarski(A_42)=C_43 | k1_xboole_0=C_43 | k2_xboole_0(B_44, C_43)!=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.34  tff(c_133, plain, (![A_42]: (k1_tarski(A_42)='#skF_2' | k1_xboole_0='#skF_2' | k1_tarski(A_42)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_95, c_130])).
% 2.28/1.34  tff(c_134, plain, (![A_42]: (k1_tarski(A_42)='#skF_2' | k1_tarski(A_42)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_120, c_133])).
% 2.28/1.34  tff(c_188, plain, (![A_55]: (k1_tarski('#skF_1'(A_55))='#skF_2' | A_55!='#skF_3' | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55) | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55))), inference(superposition, [status(thm), theory('equality')], [c_166, c_134])).
% 2.28/1.34  tff(c_157, plain, (![A_53]: (k1_tarski('#skF_1'(A_53))=A_53 | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_151, c_36])).
% 2.28/1.34  tff(c_283, plain, (![A_71]: (A_71='#skF_2' | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | A_71!='#skF_3' | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71) | ~v1_zfmisc_1(A_71) | v1_xboole_0(A_71))), inference(superposition, [status(thm), theory('equality')], [c_188, c_157])).
% 2.28/1.34  tff(c_285, plain, ('#skF_2'='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_283])).
% 2.28/1.34  tff(c_288, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_285])).
% 2.28/1.34  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_288])).
% 2.28/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.34  
% 2.28/1.34  Inference rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Ref     : 3
% 2.28/1.34  #Sup     : 54
% 2.28/1.34  #Fact    : 0
% 2.28/1.34  #Define  : 0
% 2.28/1.34  #Split   : 1
% 2.28/1.34  #Chain   : 0
% 2.28/1.34  #Close   : 0
% 2.28/1.34  
% 2.28/1.34  Ordering : KBO
% 2.28/1.34  
% 2.28/1.34  Simplification rules
% 2.28/1.34  ----------------------
% 2.28/1.34  #Subsume      : 13
% 2.28/1.34  #Demod        : 18
% 2.28/1.34  #Tautology    : 28
% 2.28/1.34  #SimpNegUnit  : 6
% 2.28/1.34  #BackRed      : 11
% 2.28/1.34  
% 2.28/1.34  #Partial instantiations: 0
% 2.28/1.34  #Strategies tried      : 1
% 2.28/1.34  
% 2.28/1.34  Timing (in seconds)
% 2.28/1.34  ----------------------
% 2.28/1.35  Preprocessing        : 0.31
% 2.28/1.35  Parsing              : 0.17
% 2.28/1.35  CNF conversion       : 0.02
% 2.28/1.35  Main loop            : 0.21
% 2.28/1.35  Inferencing          : 0.08
% 2.28/1.35  Reduction            : 0.06
% 2.28/1.35  Demodulation         : 0.04
% 2.28/1.35  BG Simplification    : 0.02
% 2.28/1.35  Subsumption          : 0.05
% 2.28/1.35  Abstraction          : 0.01
% 2.28/1.35  MUC search           : 0.00
% 2.28/1.35  Cooper               : 0.00
% 2.28/1.35  Total                : 0.55
% 2.28/1.35  Index Insertion      : 0.00
% 2.28/1.35  Index Deletion       : 0.00
% 2.28/1.35  Index Matching       : 0.00
% 2.28/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
