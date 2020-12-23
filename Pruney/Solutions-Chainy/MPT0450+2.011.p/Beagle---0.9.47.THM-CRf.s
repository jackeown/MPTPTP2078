%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:37 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 142 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 246 expanded)
%              Number of equality atoms :    9 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,k3_xboole_0(B_60,C_61))
      | ~ r1_tarski(A_59,C_61)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_121,plain,(
    ! [B_60,C_61] :
      ( k3_xboole_0(B_60,C_61) = B_60
      | ~ r1_tarski(B_60,C_61)
      | ~ r1_tarski(B_60,B_60) ) ),
    inference(resolution,[status(thm)],[c_117,c_102])).

tff(c_136,plain,(
    ! [B_62,C_63] :
      ( k3_xboole_0(B_62,C_63) = B_62
      | ~ r1_tarski(B_62,C_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_291,plain,(
    ! [B_73] : k3_xboole_0(B_73,B_73) = B_73 ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_306,plain,(
    ! [B_73] : k2_xboole_0(B_73,B_73) = B_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_12])).

tff(c_379,plain,(
    ! [A_77,B_78,C_79] : r1_tarski(k2_xboole_0(k3_xboole_0(A_77,B_78),k3_xboole_0(A_77,C_79)),k2_xboole_0(B_78,C_79)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_400,plain,(
    ! [A_77,B_73] : r1_tarski(k2_xboole_0(k3_xboole_0(A_77,B_73),k3_xboole_0(A_77,B_73)),B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_379])).

tff(c_455,plain,(
    ! [A_84,B_85] : r1_tarski(k3_xboole_0(A_84,B_85),B_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_400])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_82,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_86,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(A_22)
      | ~ v1_relat_1(B_23)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_82])).

tff(c_472,plain,(
    ! [A_84,B_85] :
      ( v1_relat_1(k3_xboole_0(A_84,B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_455,c_86])).

tff(c_415,plain,(
    ! [A_77,B_73] : r1_tarski(k3_xboole_0(A_77,B_73),B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_400])).

tff(c_417,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(k3_relat_1(A_80),k3_relat_1(B_81))
      | ~ r1_tarski(A_80,B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(A_48)
      | ~ v1_relat_1(B_49)
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_26,c_82])).

tff(c_94,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_264,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k3_relat_1(A_71),k3_relat_1(B_72))
      | ~ r1_tarski(A_71,B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_135,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_117,c_32])).

tff(c_149,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_267,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_264,c_149])).

tff(c_278,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8,c_267])).

tff(c_284,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_278])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_284])).

tff(c_289,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_420,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_417,c_289])).

tff(c_431,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_420])).

tff(c_955,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_431])).

tff(c_958,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_472,c_955])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_958])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.40  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.86/1.40  
% 2.86/1.40  %Foreground sorts:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Background operators:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Foreground operators:
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.86/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.86/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.86/1.40  
% 2.86/1.41  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.86/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.86/1.41  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.86/1.41  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.86/1.41  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.86/1.41  tff(f_43, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.86/1.41  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.86/1.41  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.86/1.41  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.86/1.41  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.86/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.41  tff(c_117, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, k3_xboole_0(B_60, C_61)) | ~r1_tarski(A_59, C_61) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.41  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.41  tff(c_97, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.41  tff(c_102, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_97])).
% 2.86/1.41  tff(c_121, plain, (![B_60, C_61]: (k3_xboole_0(B_60, C_61)=B_60 | ~r1_tarski(B_60, C_61) | ~r1_tarski(B_60, B_60))), inference(resolution, [status(thm)], [c_117, c_102])).
% 2.86/1.41  tff(c_136, plain, (![B_62, C_63]: (k3_xboole_0(B_62, C_63)=B_62 | ~r1_tarski(B_62, C_63))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_121])).
% 2.86/1.41  tff(c_291, plain, (![B_73]: (k3_xboole_0(B_73, B_73)=B_73)), inference(resolution, [status(thm)], [c_6, c_136])).
% 2.86/1.41  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.41  tff(c_306, plain, (![B_73]: (k2_xboole_0(B_73, B_73)=B_73)), inference(superposition, [status(thm), theory('equality')], [c_291, c_12])).
% 2.86/1.41  tff(c_379, plain, (![A_77, B_78, C_79]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_77, B_78), k3_xboole_0(A_77, C_79)), k2_xboole_0(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.41  tff(c_400, plain, (![A_77, B_73]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_77, B_73), k3_xboole_0(A_77, B_73)), B_73))), inference(superposition, [status(thm), theory('equality')], [c_306, c_379])).
% 2.86/1.41  tff(c_455, plain, (![A_84, B_85]: (r1_tarski(k3_xboole_0(A_84, B_85), B_85))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_400])).
% 2.86/1.41  tff(c_26, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.41  tff(c_82, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.41  tff(c_86, plain, (![A_22, B_23]: (v1_relat_1(A_22) | ~v1_relat_1(B_23) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_26, c_82])).
% 2.86/1.41  tff(c_472, plain, (![A_84, B_85]: (v1_relat_1(k3_xboole_0(A_84, B_85)) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_455, c_86])).
% 2.86/1.41  tff(c_415, plain, (![A_77, B_73]: (r1_tarski(k3_xboole_0(A_77, B_73), B_73))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_400])).
% 2.86/1.41  tff(c_417, plain, (![A_80, B_81]: (r1_tarski(k3_relat_1(A_80), k3_relat_1(B_81)) | ~r1_tarski(A_80, B_81) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.41  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.86/1.41  tff(c_87, plain, (![A_48, B_49]: (v1_relat_1(A_48) | ~v1_relat_1(B_49) | ~r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_26, c_82])).
% 2.86/1.41  tff(c_94, plain, (![A_3, B_4]: (v1_relat_1(k3_xboole_0(A_3, B_4)) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_8, c_87])).
% 2.86/1.41  tff(c_264, plain, (![A_71, B_72]: (r1_tarski(k3_relat_1(A_71), k3_relat_1(B_72)) | ~r1_tarski(A_71, B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.41  tff(c_32, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.86/1.41  tff(c_135, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_32])).
% 2.86/1.41  tff(c_149, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.86/1.41  tff(c_267, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_264, c_149])).
% 2.86/1.41  tff(c_278, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8, c_267])).
% 2.86/1.41  tff(c_284, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_94, c_278])).
% 2.86/1.41  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_284])).
% 2.86/1.41  tff(c_289, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_135])).
% 2.86/1.41  tff(c_420, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_417, c_289])).
% 2.86/1.41  tff(c_431, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_420])).
% 2.86/1.41  tff(c_955, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_431])).
% 2.86/1.41  tff(c_958, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_472, c_955])).
% 2.86/1.41  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_958])).
% 2.86/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  Inference rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Ref     : 0
% 2.86/1.41  #Sup     : 228
% 2.86/1.41  #Fact    : 0
% 2.86/1.41  #Define  : 0
% 2.86/1.41  #Split   : 3
% 2.86/1.41  #Chain   : 0
% 2.86/1.41  #Close   : 0
% 2.86/1.41  
% 2.86/1.41  Ordering : KBO
% 2.86/1.41  
% 2.86/1.41  Simplification rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Subsume      : 13
% 2.86/1.41  #Demod        : 150
% 2.86/1.41  #Tautology    : 140
% 2.86/1.41  #SimpNegUnit  : 0
% 2.86/1.41  #BackRed      : 0
% 2.86/1.41  
% 2.86/1.41  #Partial instantiations: 0
% 2.86/1.41  #Strategies tried      : 1
% 2.86/1.41  
% 2.86/1.41  Timing (in seconds)
% 2.86/1.41  ----------------------
% 2.86/1.42  Preprocessing        : 0.31
% 2.86/1.42  Parsing              : 0.17
% 2.86/1.42  CNF conversion       : 0.02
% 2.86/1.42  Main loop            : 0.33
% 2.86/1.42  Inferencing          : 0.12
% 2.86/1.42  Reduction            : 0.11
% 2.86/1.42  Demodulation         : 0.08
% 2.86/1.42  BG Simplification    : 0.02
% 2.86/1.42  Subsumption          : 0.06
% 2.86/1.42  Abstraction          : 0.02
% 2.86/1.42  MUC search           : 0.00
% 2.86/1.42  Cooper               : 0.00
% 2.86/1.42  Total                : 0.66
% 2.86/1.42  Index Insertion      : 0.00
% 2.86/1.42  Index Deletion       : 0.00
% 2.86/1.42  Index Matching       : 0.00
% 2.86/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
