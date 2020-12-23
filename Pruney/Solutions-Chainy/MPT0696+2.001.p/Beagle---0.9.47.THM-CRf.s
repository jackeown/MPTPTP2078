%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:58 EST 2020

% Result     : Theorem 11.26s
% Output     : CNFRefutation 11.26s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 151 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 311 expanded)
%              Number of equality atoms :    7 (  23 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k3_xboole_0(A,k10_relat_1(C,B)),k10_relat_1(C,k3_xboole_0(k9_relat_1(C,A),B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k7_relat_1(B_18,A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_41,plain,(
    ! [A_31,B_32] :
      ( v1_relat_1(A_31)
      | ~ v1_relat_1(B_32)
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

tff(c_48,plain,(
    ! [B_18,A_17] :
      ( v1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_104,plain,(
    ! [C_46,A_47,D_48,B_49] :
      ( r1_tarski(k10_relat_1(C_46,A_47),k10_relat_1(D_48,B_49))
      | ~ r1_tarski(A_47,B_49)
      | ~ r1_tarski(C_46,D_48)
      | ~ v1_relat_1(D_48)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,(
    ! [A_43,C_44,B_45] :
      ( k3_xboole_0(A_43,k10_relat_1(C_44,B_45)) = k10_relat_1(k7_relat_1(C_44,A_43),B_45)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),k10_relat_1('#skF_3',k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k10_relat_1('#skF_3',k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_24])).

tff(c_102,plain,(
    ~ r1_tarski(k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k10_relat_1('#skF_3',k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_93])).

tff(c_107,plain,
    ( ~ r1_tarski('#skF_2',k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_104,c_102])).

tff(c_121,plain,
    ( ~ r1_tarski('#skF_2',k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_107])).

tff(c_124,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_127,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_127])).

tff(c_133,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k10_relat_1(B_11,k3_xboole_0(k2_relat_1(B_11),A_10)) = k10_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_293,plain,(
    ! [C_73,A_74,B_75,A_76] :
      ( r1_tarski(k10_relat_1(C_73,A_74),k10_relat_1(B_75,A_76))
      | ~ r1_tarski(A_74,k3_xboole_0(k2_relat_1(B_75),A_76))
      | ~ r1_tarski(C_73,B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(C_73)
      | ~ v1_relat_1(B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_296,plain,
    ( ~ r1_tarski('#skF_2',k3_xboole_0(k2_relat_1('#skF_3'),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_293,c_102])).

tff(c_328,plain,
    ( ~ r1_tarski('#skF_2',k3_xboole_0(k2_relat_1('#skF_3'),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_133,c_296])).

tff(c_331,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_334,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_331])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_334])).

tff(c_340,plain,(
    r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_232,plain,(
    ! [B_63,A_64,D_65,B_66] :
      ( r1_tarski(k10_relat_1(B_63,A_64),k10_relat_1(D_65,B_66))
      | ~ r1_tarski(k3_xboole_0(k2_relat_1(B_63),A_64),B_66)
      | ~ r1_tarski(B_63,D_65)
      | ~ v1_relat_1(D_65)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_14385,plain,(
    ! [D_529,B_527,A_530,A_526,B_528] :
      ( r1_tarski(k10_relat_1(k7_relat_1(B_528,A_526),A_530),k10_relat_1(D_529,B_527))
      | ~ r1_tarski(k3_xboole_0(k9_relat_1(B_528,A_526),A_530),B_527)
      | ~ r1_tarski(k7_relat_1(B_528,A_526),D_529)
      | ~ v1_relat_1(D_529)
      | ~ v1_relat_1(k7_relat_1(B_528,A_526))
      | ~ v1_relat_1(k7_relat_1(B_528,A_526))
      | ~ v1_relat_1(B_528) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_232])).

tff(c_14410,plain,
    ( ~ r1_tarski(k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2'),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14385,c_102])).

tff(c_14534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_133,c_340,c_6,c_14410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.26/4.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.26/4.11  
% 11.26/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.26/4.11  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 11.26/4.11  
% 11.26/4.11  %Foreground sorts:
% 11.26/4.11  
% 11.26/4.11  
% 11.26/4.11  %Background operators:
% 11.26/4.11  
% 11.26/4.11  
% 11.26/4.11  %Foreground operators:
% 11.26/4.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.26/4.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.26/4.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.26/4.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.26/4.11  tff('#skF_2', type, '#skF_2': $i).
% 11.26/4.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.26/4.11  tff('#skF_3', type, '#skF_3': $i).
% 11.26/4.11  tff('#skF_1', type, '#skF_1': $i).
% 11.26/4.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.26/4.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.26/4.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.26/4.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.26/4.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.26/4.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.26/4.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.26/4.11  
% 11.26/4.12  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k3_xboole_0(A, k10_relat_1(C, B)), k10_relat_1(C, k3_xboole_0(k9_relat_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_funct_1)).
% 11.26/4.12  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 11.26/4.12  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.26/4.12  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.26/4.12  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t180_relat_1)).
% 11.26/4.12  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 11.26/4.12  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 11.26/4.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.26/4.12  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 11.26/4.12  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.26/4.12  tff(c_20, plain, (![B_18, A_17]: (r1_tarski(k7_relat_1(B_18, A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.26/4.12  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.26/4.12  tff(c_36, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.26/4.12  tff(c_41, plain, (![A_31, B_32]: (v1_relat_1(A_31) | ~v1_relat_1(B_32) | ~r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_10, c_36])).
% 11.26/4.12  tff(c_48, plain, (![B_18, A_17]: (v1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_20, c_41])).
% 11.26/4.12  tff(c_104, plain, (![C_46, A_47, D_48, B_49]: (r1_tarski(k10_relat_1(C_46, A_47), k10_relat_1(D_48, B_49)) | ~r1_tarski(A_47, B_49) | ~r1_tarski(C_46, D_48) | ~v1_relat_1(D_48) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.26/4.12  tff(c_83, plain, (![A_43, C_44, B_45]: (k3_xboole_0(A_43, k10_relat_1(C_44, B_45))=k10_relat_1(k7_relat_1(C_44, A_43), B_45) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.26/4.12  tff(c_24, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), k10_relat_1('#skF_3', k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.26/4.12  tff(c_93, plain, (~r1_tarski(k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k10_relat_1('#skF_3', k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_83, c_24])).
% 11.26/4.12  tff(c_102, plain, (~r1_tarski(k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k10_relat_1('#skF_3', k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_93])).
% 11.26/4.12  tff(c_107, plain, (~r1_tarski('#skF_2', k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_104, c_102])).
% 11.26/4.12  tff(c_121, plain, (~r1_tarski('#skF_2', k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_107])).
% 11.26/4.12  tff(c_124, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_121])).
% 11.26/4.12  tff(c_127, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_124])).
% 11.26/4.12  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_127])).
% 11.26/4.12  tff(c_133, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_121])).
% 11.26/4.12  tff(c_16, plain, (![B_11, A_10]: (k10_relat_1(B_11, k3_xboole_0(k2_relat_1(B_11), A_10))=k10_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.26/4.12  tff(c_293, plain, (![C_73, A_74, B_75, A_76]: (r1_tarski(k10_relat_1(C_73, A_74), k10_relat_1(B_75, A_76)) | ~r1_tarski(A_74, k3_xboole_0(k2_relat_1(B_75), A_76)) | ~r1_tarski(C_73, B_75) | ~v1_relat_1(B_75) | ~v1_relat_1(C_73) | ~v1_relat_1(B_75))), inference(superposition, [status(thm), theory('equality')], [c_16, c_104])).
% 11.26/4.12  tff(c_296, plain, (~r1_tarski('#skF_2', k3_xboole_0(k2_relat_1('#skF_3'), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_293, c_102])).
% 11.26/4.12  tff(c_328, plain, (~r1_tarski('#skF_2', k3_xboole_0(k2_relat_1('#skF_3'), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_133, c_296])).
% 11.26/4.12  tff(c_331, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_328])).
% 11.26/4.12  tff(c_334, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_331])).
% 11.26/4.12  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_334])).
% 11.26/4.12  tff(c_340, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_328])).
% 11.26/4.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.26/4.12  tff(c_14, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.26/4.12  tff(c_232, plain, (![B_63, A_64, D_65, B_66]: (r1_tarski(k10_relat_1(B_63, A_64), k10_relat_1(D_65, B_66)) | ~r1_tarski(k3_xboole_0(k2_relat_1(B_63), A_64), B_66) | ~r1_tarski(B_63, D_65) | ~v1_relat_1(D_65) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_16, c_104])).
% 11.26/4.12  tff(c_14385, plain, (![D_529, B_527, A_530, A_526, B_528]: (r1_tarski(k10_relat_1(k7_relat_1(B_528, A_526), A_530), k10_relat_1(D_529, B_527)) | ~r1_tarski(k3_xboole_0(k9_relat_1(B_528, A_526), A_530), B_527) | ~r1_tarski(k7_relat_1(B_528, A_526), D_529) | ~v1_relat_1(D_529) | ~v1_relat_1(k7_relat_1(B_528, A_526)) | ~v1_relat_1(k7_relat_1(B_528, A_526)) | ~v1_relat_1(B_528))), inference(superposition, [status(thm), theory('equality')], [c_14, c_232])).
% 11.26/4.12  tff(c_14410, plain, (~r1_tarski(k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14385, c_102])).
% 11.26/4.12  tff(c_14534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_133, c_340, c_6, c_14410])).
% 11.26/4.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.26/4.12  
% 11.26/4.12  Inference rules
% 11.26/4.12  ----------------------
% 11.26/4.12  #Ref     : 0
% 11.26/4.12  #Sup     : 3679
% 11.26/4.12  #Fact    : 0
% 11.26/4.12  #Define  : 0
% 11.26/4.12  #Split   : 6
% 11.26/4.12  #Chain   : 0
% 11.26/4.12  #Close   : 0
% 11.26/4.12  
% 11.26/4.12  Ordering : KBO
% 11.26/4.12  
% 11.26/4.12  Simplification rules
% 11.26/4.12  ----------------------
% 11.26/4.12  #Subsume      : 497
% 11.26/4.12  #Demod        : 983
% 11.26/4.12  #Tautology    : 138
% 11.26/4.12  #SimpNegUnit  : 0
% 11.26/4.12  #BackRed      : 0
% 11.26/4.12  
% 11.26/4.12  #Partial instantiations: 0
% 11.26/4.12  #Strategies tried      : 1
% 11.26/4.12  
% 11.26/4.12  Timing (in seconds)
% 11.26/4.12  ----------------------
% 11.26/4.13  Preprocessing        : 0.29
% 11.26/4.13  Parsing              : 0.16
% 11.26/4.13  CNF conversion       : 0.02
% 11.26/4.13  Main loop            : 3.06
% 11.26/4.13  Inferencing          : 0.84
% 11.26/4.13  Reduction            : 0.64
% 11.26/4.13  Demodulation         : 0.43
% 11.26/4.13  BG Simplification    : 0.12
% 11.26/4.13  Subsumption          : 1.29
% 11.26/4.13  Abstraction          : 0.13
% 11.26/4.13  MUC search           : 0.00
% 11.26/4.13  Cooper               : 0.00
% 11.26/4.13  Total                : 3.38
% 11.26/4.13  Index Insertion      : 0.00
% 11.26/4.13  Index Deletion       : 0.00
% 11.26/4.13  Index Matching       : 0.00
% 11.26/4.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
