%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:20 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   58 (  86 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 131 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_35,A_1] :
      ( r1_tarski(A_35,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_35,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_77,plain,(
    ! [A_37,A_38] :
      ( r1_tarski(A_37,A_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_38)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_73])).

tff(c_81,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_32,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_82,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = B_39
      | ~ v4_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_24] :
      ( k7_relat_1(k6_relat_1(A_24),A_24) = k6_relat_1(A_24)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_34,c_82])).

tff(c_88,plain,(
    ! [A_24] : k7_relat_1(k6_relat_1(A_24),A_24) = k6_relat_1(A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_85])).

tff(c_98,plain,(
    ! [B_42,A_43] :
      ( k2_relat_1(k7_relat_1(B_42,A_43)) = k9_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_24] :
      ( k9_relat_1(k6_relat_1(A_24),A_24) = k2_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_98])).

tff(c_111,plain,(
    ! [A_24] : k9_relat_1(k6_relat_1(A_24),A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_107])).

tff(c_139,plain,(
    ! [B_50,A_51] :
      ( k5_relat_1(B_50,k6_relat_1(A_51)) = B_50
      | ~ r1_tarski(k2_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_145,plain,(
    ! [A_21,A_51] :
      ( k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_51)) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_51)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_139])).

tff(c_147,plain,(
    ! [A_21,A_51] :
      ( k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_51)) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_145])).

tff(c_397,plain,(
    ! [B_81,C_82,A_83] :
      ( k9_relat_1(k5_relat_1(B_81,C_82),A_83) = k9_relat_1(C_82,k9_relat_1(B_81,A_83))
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_406,plain,(
    ! [A_51,A_21,A_83] :
      ( k9_relat_1(k6_relat_1(A_51),k9_relat_1(k6_relat_1(A_21),A_83)) = k9_relat_1(k6_relat_1(A_21),A_83)
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ r1_tarski(A_21,A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_397])).

tff(c_411,plain,(
    ! [A_84,A_85,A_86] :
      ( k9_relat_1(k6_relat_1(A_84),k9_relat_1(k6_relat_1(A_85),A_86)) = k9_relat_1(k6_relat_1(A_85),A_86)
      | ~ r1_tarski(A_85,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_406])).

tff(c_453,plain,(
    ! [A_84,A_24] :
      ( k9_relat_1(k6_relat_1(A_84),A_24) = k9_relat_1(k6_relat_1(A_24),A_24)
      | ~ r1_tarski(A_24,A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_411])).

tff(c_570,plain,(
    ! [A_89,A_90] :
      ( k9_relat_1(k6_relat_1(A_89),A_90) = A_90
      | ~ r1_tarski(A_90,A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_453])).

tff(c_38,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_604,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_38])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.33  
% 2.66/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.33  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.66/1.33  
% 2.66/1.33  %Foreground sorts:
% 2.66/1.33  
% 2.66/1.33  
% 2.66/1.33  %Background operators:
% 2.66/1.33  
% 2.66/1.33  
% 2.66/1.33  %Foreground operators:
% 2.66/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.66/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.66/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.66/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.66/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.66/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.33  
% 2.66/1.34  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.66/1.34  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.66/1.34  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.66/1.34  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.66/1.34  tff(f_83, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 2.66/1.34  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.66/1.34  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.66/1.34  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.66/1.34  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.66/1.34  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.66/1.34  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.34  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.34  tff(c_69, plain, (![A_35, B_36]: (r2_hidden(A_35, B_36) | v1_xboole_0(B_36) | ~m1_subset_1(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.34  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.34  tff(c_73, plain, (![A_35, A_1]: (r1_tarski(A_35, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_35, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_69, c_2])).
% 2.66/1.34  tff(c_77, plain, (![A_37, A_38]: (r1_tarski(A_37, A_38) | ~m1_subset_1(A_37, k1_zfmisc_1(A_38)))), inference(negUnitSimplification, [status(thm)], [c_14, c_73])).
% 2.66/1.34  tff(c_81, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_77])).
% 2.66/1.34  tff(c_32, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.34  tff(c_28, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.66/1.34  tff(c_34, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.34  tff(c_82, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=B_39 | ~v4_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.66/1.34  tff(c_85, plain, (![A_24]: (k7_relat_1(k6_relat_1(A_24), A_24)=k6_relat_1(A_24) | ~v1_relat_1(k6_relat_1(A_24)))), inference(resolution, [status(thm)], [c_34, c_82])).
% 2.66/1.34  tff(c_88, plain, (![A_24]: (k7_relat_1(k6_relat_1(A_24), A_24)=k6_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_85])).
% 2.66/1.34  tff(c_98, plain, (![B_42, A_43]: (k2_relat_1(k7_relat_1(B_42, A_43))=k9_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.34  tff(c_107, plain, (![A_24]: (k9_relat_1(k6_relat_1(A_24), A_24)=k2_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_98])).
% 2.66/1.34  tff(c_111, plain, (![A_24]: (k9_relat_1(k6_relat_1(A_24), A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_107])).
% 2.66/1.34  tff(c_139, plain, (![B_50, A_51]: (k5_relat_1(B_50, k6_relat_1(A_51))=B_50 | ~r1_tarski(k2_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.66/1.34  tff(c_145, plain, (![A_21, A_51]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_51))=k6_relat_1(A_21) | ~r1_tarski(A_21, A_51) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_139])).
% 2.66/1.34  tff(c_147, plain, (![A_21, A_51]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_51))=k6_relat_1(A_21) | ~r1_tarski(A_21, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_145])).
% 2.66/1.34  tff(c_397, plain, (![B_81, C_82, A_83]: (k9_relat_1(k5_relat_1(B_81, C_82), A_83)=k9_relat_1(C_82, k9_relat_1(B_81, A_83)) | ~v1_relat_1(C_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.66/1.34  tff(c_406, plain, (![A_51, A_21, A_83]: (k9_relat_1(k6_relat_1(A_51), k9_relat_1(k6_relat_1(A_21), A_83))=k9_relat_1(k6_relat_1(A_21), A_83) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_21)) | ~r1_tarski(A_21, A_51))), inference(superposition, [status(thm), theory('equality')], [c_147, c_397])).
% 2.66/1.34  tff(c_411, plain, (![A_84, A_85, A_86]: (k9_relat_1(k6_relat_1(A_84), k9_relat_1(k6_relat_1(A_85), A_86))=k9_relat_1(k6_relat_1(A_85), A_86) | ~r1_tarski(A_85, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_406])).
% 2.66/1.34  tff(c_453, plain, (![A_84, A_24]: (k9_relat_1(k6_relat_1(A_84), A_24)=k9_relat_1(k6_relat_1(A_24), A_24) | ~r1_tarski(A_24, A_84))), inference(superposition, [status(thm), theory('equality')], [c_111, c_411])).
% 2.66/1.34  tff(c_570, plain, (![A_89, A_90]: (k9_relat_1(k6_relat_1(A_89), A_90)=A_90 | ~r1_tarski(A_90, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_453])).
% 2.66/1.34  tff(c_38, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.34  tff(c_604, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_38])).
% 2.66/1.34  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_604])).
% 2.66/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.34  
% 2.66/1.34  Inference rules
% 2.66/1.34  ----------------------
% 2.66/1.34  #Ref     : 0
% 2.66/1.34  #Sup     : 139
% 2.66/1.34  #Fact    : 0
% 2.66/1.34  #Define  : 0
% 2.66/1.34  #Split   : 1
% 2.66/1.34  #Chain   : 0
% 2.66/1.34  #Close   : 0
% 2.66/1.34  
% 2.66/1.34  Ordering : KBO
% 2.66/1.34  
% 2.66/1.34  Simplification rules
% 2.66/1.34  ----------------------
% 2.66/1.34  #Subsume      : 19
% 2.66/1.34  #Demod        : 28
% 2.66/1.34  #Tautology    : 56
% 2.66/1.34  #SimpNegUnit  : 1
% 2.66/1.34  #BackRed      : 0
% 2.66/1.34  
% 2.66/1.34  #Partial instantiations: 0
% 2.66/1.34  #Strategies tried      : 1
% 2.66/1.34  
% 2.66/1.34  Timing (in seconds)
% 2.66/1.34  ----------------------
% 2.66/1.35  Preprocessing        : 0.29
% 2.66/1.35  Parsing              : 0.16
% 2.66/1.35  CNF conversion       : 0.02
% 2.66/1.35  Main loop            : 0.29
% 2.66/1.35  Inferencing          : 0.12
% 2.66/1.35  Reduction            : 0.07
% 2.66/1.35  Demodulation         : 0.05
% 2.66/1.35  BG Simplification    : 0.02
% 2.66/1.35  Subsumption          : 0.05
% 2.66/1.35  Abstraction          : 0.01
% 2.66/1.35  MUC search           : 0.00
% 2.66/1.35  Cooper               : 0.00
% 2.66/1.35  Total                : 0.61
% 2.66/1.35  Index Insertion      : 0.00
% 2.66/1.35  Index Deletion       : 0.00
% 2.66/1.35  Index Matching       : 0.00
% 2.66/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
