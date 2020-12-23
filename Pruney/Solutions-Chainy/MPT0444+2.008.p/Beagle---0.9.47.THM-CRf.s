%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:21 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 101 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 162 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    ! [B_58,A_57] : r2_hidden(B_58,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_8])).

tff(c_46,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k1_setfam_1(B_38),A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    ! [A_73,B_74] :
      ( v1_relat_1(A_73)
      | ~ v1_relat_1(B_74)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_118,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(k1_setfam_1(B_77))
      | ~ v1_relat_1(A_78)
      | ~ r2_hidden(A_78,B_77) ) ),
    inference(resolution,[status(thm)],[c_46,c_108])).

tff(c_120,plain,(
    ! [A_57,B_58] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_57,B_58)))
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_72,c_118])).

tff(c_130,plain,(
    ! [A_57,B_58] :
      ( v1_relat_1(k3_xboole_0(A_57,B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_120])).

tff(c_99,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_setfam_1(B_69),A_70)
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_161,plain,(
    ! [A_93,B_94,A_95] :
      ( r1_tarski(k3_xboole_0(A_93,B_94),A_95)
      | ~ r2_hidden(A_95,k2_tarski(A_93,B_94)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_99])).

tff(c_168,plain,(
    ! [A_57,B_58] : r1_tarski(k3_xboole_0(A_57,B_58),B_58) ),
    inference(resolution,[status(thm)],[c_72,c_161])).

tff(c_288,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k2_relat_1(A_123),k2_relat_1(B_124))
      | ~ r1_tarski(A_123,B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_230,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(k2_relat_1(A_114),k2_relat_1(B_115))
      | ~ r1_tarski(A_114,B_115)
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_171,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_tarski(A_96,k3_xboole_0(B_97,C_98))
      | ~ r1_tarski(A_96,C_98)
      | ~ r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_179,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_171,c_54])).

tff(c_199,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_233,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_230,c_199])).

tff(c_239,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2,c_233])).

tff(c_243,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_239])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_243])).

tff(c_251,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_291,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_288,c_251])).

tff(c_297,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_168,c_291])).

tff(c_301,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_297])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.40  
% 2.21/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.21/1.40  
% 2.21/1.40  %Foreground sorts:
% 2.21/1.40  
% 2.21/1.40  
% 2.21/1.40  %Background operators:
% 2.21/1.40  
% 2.21/1.40  
% 2.21/1.40  %Foreground operators:
% 2.21/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.21/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.21/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.21/1.40  
% 2.21/1.41  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.21/1.41  tff(f_60, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.21/1.41  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.21/1.41  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.21/1.41  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.21/1.41  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.21/1.41  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.21/1.41  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.21/1.41  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.21/1.41  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.21/1.41  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.41  tff(c_40, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.41  tff(c_63, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.41  tff(c_8, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.41  tff(c_72, plain, (![B_58, A_57]: (r2_hidden(B_58, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_8])).
% 2.21/1.41  tff(c_46, plain, (![B_38, A_37]: (r1_tarski(k1_setfam_1(B_38), A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.21/1.41  tff(c_44, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.41  tff(c_103, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.41  tff(c_108, plain, (![A_73, B_74]: (v1_relat_1(A_73) | ~v1_relat_1(B_74) | ~r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_44, c_103])).
% 2.21/1.41  tff(c_118, plain, (![B_77, A_78]: (v1_relat_1(k1_setfam_1(B_77)) | ~v1_relat_1(A_78) | ~r2_hidden(A_78, B_77))), inference(resolution, [status(thm)], [c_46, c_108])).
% 2.21/1.41  tff(c_120, plain, (![A_57, B_58]: (v1_relat_1(k1_setfam_1(k2_tarski(A_57, B_58))) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_72, c_118])).
% 2.21/1.41  tff(c_130, plain, (![A_57, B_58]: (v1_relat_1(k3_xboole_0(A_57, B_58)) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_120])).
% 2.21/1.41  tff(c_99, plain, (![B_69, A_70]: (r1_tarski(k1_setfam_1(B_69), A_70) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.21/1.41  tff(c_161, plain, (![A_93, B_94, A_95]: (r1_tarski(k3_xboole_0(A_93, B_94), A_95) | ~r2_hidden(A_95, k2_tarski(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_99])).
% 2.21/1.41  tff(c_168, plain, (![A_57, B_58]: (r1_tarski(k3_xboole_0(A_57, B_58), B_58))), inference(resolution, [status(thm)], [c_72, c_161])).
% 2.21/1.41  tff(c_288, plain, (![A_123, B_124]: (r1_tarski(k2_relat_1(A_123), k2_relat_1(B_124)) | ~r1_tarski(A_123, B_124) | ~v1_relat_1(B_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.41  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.41  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.41  tff(c_230, plain, (![A_114, B_115]: (r1_tarski(k2_relat_1(A_114), k2_relat_1(B_115)) | ~r1_tarski(A_114, B_115) | ~v1_relat_1(B_115) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.21/1.41  tff(c_171, plain, (![A_96, B_97, C_98]: (r1_tarski(A_96, k3_xboole_0(B_97, C_98)) | ~r1_tarski(A_96, C_98) | ~r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.41  tff(c_54, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.41  tff(c_179, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_171, c_54])).
% 2.21/1.41  tff(c_199, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_179])).
% 2.21/1.41  tff(c_233, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_230, c_199])).
% 2.21/1.41  tff(c_239, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2, c_233])).
% 2.21/1.41  tff(c_243, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_130, c_239])).
% 2.21/1.41  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_243])).
% 2.21/1.41  tff(c_251, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_179])).
% 2.21/1.41  tff(c_291, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_288, c_251])).
% 2.21/1.41  tff(c_297, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_168, c_291])).
% 2.21/1.41  tff(c_301, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_130, c_297])).
% 2.21/1.41  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_301])).
% 2.21/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.41  
% 2.21/1.41  Inference rules
% 2.21/1.41  ----------------------
% 2.21/1.41  #Ref     : 0
% 2.21/1.41  #Sup     : 51
% 2.21/1.41  #Fact    : 0
% 2.21/1.41  #Define  : 0
% 2.21/1.41  #Split   : 2
% 2.21/1.41  #Chain   : 0
% 2.21/1.41  #Close   : 0
% 2.21/1.41  
% 2.21/1.41  Ordering : KBO
% 2.21/1.41  
% 2.21/1.41  Simplification rules
% 2.21/1.41  ----------------------
% 2.21/1.41  #Subsume      : 5
% 2.21/1.41  #Demod        : 13
% 2.21/1.41  #Tautology    : 21
% 2.21/1.41  #SimpNegUnit  : 0
% 2.21/1.41  #BackRed      : 0
% 2.21/1.41  
% 2.21/1.41  #Partial instantiations: 0
% 2.21/1.41  #Strategies tried      : 1
% 2.21/1.41  
% 2.21/1.41  Timing (in seconds)
% 2.21/1.41  ----------------------
% 2.21/1.42  Preprocessing        : 0.33
% 2.21/1.42  Parsing              : 0.18
% 2.21/1.42  CNF conversion       : 0.02
% 2.21/1.42  Main loop            : 0.21
% 2.21/1.42  Inferencing          : 0.07
% 2.21/1.42  Reduction            : 0.06
% 2.21/1.42  Demodulation         : 0.05
% 2.21/1.42  BG Simplification    : 0.01
% 2.21/1.42  Subsumption          : 0.04
% 2.21/1.42  Abstraction          : 0.01
% 2.21/1.42  MUC search           : 0.00
% 2.21/1.42  Cooper               : 0.00
% 2.21/1.42  Total                : 0.57
% 2.21/1.42  Index Insertion      : 0.00
% 2.21/1.42  Index Deletion       : 0.00
% 2.21/1.42  Index Matching       : 0.00
% 2.21/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
