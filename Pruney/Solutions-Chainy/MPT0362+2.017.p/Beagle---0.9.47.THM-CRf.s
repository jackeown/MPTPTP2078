%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:34 EST 2020

% Result     : Theorem 6.12s
% Output     : CNFRefutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :   58 (  70 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 104 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_8,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [B_36,A_11] :
      ( r1_tarski(B_36,A_11)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_63,c_10])).

tff(c_71,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(B_38,A_39)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_67])).

tff(c_84,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_71])).

tff(c_124,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,'#skF_3')
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_84,c_124])).

tff(c_12,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(B_44,A_45)
      | ~ r2_hidden(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_110,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_114,plain,(
    ! [C_15,A_11] :
      ( m1_subset_1(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_110])).

tff(c_218,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_742,plain,(
    ! [A_106,C_107] :
      ( k4_xboole_0(A_106,C_107) = k3_subset_1(A_106,C_107)
      | ~ r1_tarski(C_107,A_106) ) ),
    inference(resolution,[status(thm)],[c_114,c_218])).

tff(c_1993,plain,(
    ! [A_181] :
      ( k4_xboole_0('#skF_3',A_181) = k3_subset_1('#skF_3',A_181)
      | ~ r1_tarski(A_181,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_742])).

tff(c_5885,plain,(
    ! [B_303] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',B_303)) = k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_303)) ),
    inference(resolution,[status(thm)],[c_6,c_1993])).

tff(c_235,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_218])).

tff(c_323,plain,(
    ! [C_73,B_74,A_75] :
      ( r1_tarski(k4_xboole_0(C_73,B_74),k4_xboole_0(C_73,A_75))
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_331,plain,(
    ! [A_75] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_3',A_75))
      | ~ r1_tarski(A_75,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_323])).

tff(c_5923,plain,(
    ! [B_303] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_303)))
      | ~ r1_tarski(k4_xboole_0('#skF_4',B_303),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5885,c_331])).

tff(c_6022,plain,(
    ! [B_306] : r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_306))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5923])).

tff(c_6039,plain,(
    ! [B_10] : r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_10))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_6022])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_427,plain,(
    ! [A_87,B_88,C_89] :
      ( k9_subset_1(A_87,B_88,C_89) = k3_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_439,plain,(
    ! [B_88] : k9_subset_1('#skF_3',B_88,'#skF_5') = k3_xboole_0(B_88,'#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_427])).

tff(c_36,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_441,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_36])).

tff(c_6489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6039,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.12/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.27  
% 6.12/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.27  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.12/2.27  
% 6.12/2.27  %Foreground sorts:
% 6.12/2.27  
% 6.12/2.27  
% 6.12/2.27  %Background operators:
% 6.12/2.27  
% 6.12/2.27  
% 6.12/2.27  %Foreground operators:
% 6.12/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.12/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.12/2.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.12/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.12/2.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.12/2.27  tff('#skF_5', type, '#skF_5': $i).
% 6.12/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.12/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.12/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.12/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.12/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.12/2.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.12/2.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.12/2.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.12/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.12/2.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.12/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.12/2.27  
% 6.12/2.28  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.12/2.28  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.12/2.28  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 6.12/2.28  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.12/2.28  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.12/2.28  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.12/2.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.12/2.28  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.12/2.28  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 6.12/2.28  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.12/2.28  tff(c_8, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.12/2.28  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.12/2.28  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.12/2.28  tff(c_32, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.12/2.28  tff(c_63, plain, (![B_36, A_37]: (r2_hidden(B_36, A_37) | ~m1_subset_1(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.12/2.28  tff(c_10, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.12/2.28  tff(c_67, plain, (![B_36, A_11]: (r1_tarski(B_36, A_11) | ~m1_subset_1(B_36, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_63, c_10])).
% 6.12/2.28  tff(c_71, plain, (![B_38, A_39]: (r1_tarski(B_38, A_39) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)))), inference(negUnitSimplification, [status(thm)], [c_32, c_67])).
% 6.12/2.28  tff(c_84, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_71])).
% 6.12/2.28  tff(c_124, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.12/2.28  tff(c_134, plain, (![A_48]: (r1_tarski(A_48, '#skF_3') | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_124])).
% 6.12/2.28  tff(c_12, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.12/2.28  tff(c_104, plain, (![B_44, A_45]: (m1_subset_1(B_44, A_45) | ~r2_hidden(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.12/2.28  tff(c_110, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_12, c_104])).
% 6.12/2.28  tff(c_114, plain, (![C_15, A_11]: (m1_subset_1(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(negUnitSimplification, [status(thm)], [c_32, c_110])).
% 6.12/2.28  tff(c_218, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.12/2.28  tff(c_742, plain, (![A_106, C_107]: (k4_xboole_0(A_106, C_107)=k3_subset_1(A_106, C_107) | ~r1_tarski(C_107, A_106))), inference(resolution, [status(thm)], [c_114, c_218])).
% 6.12/2.28  tff(c_1993, plain, (![A_181]: (k4_xboole_0('#skF_3', A_181)=k3_subset_1('#skF_3', A_181) | ~r1_tarski(A_181, '#skF_4'))), inference(resolution, [status(thm)], [c_134, c_742])).
% 6.12/2.28  tff(c_5885, plain, (![B_303]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', B_303))=k3_subset_1('#skF_3', k4_xboole_0('#skF_4', B_303)))), inference(resolution, [status(thm)], [c_6, c_1993])).
% 6.12/2.28  tff(c_235, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_218])).
% 6.12/2.28  tff(c_323, plain, (![C_73, B_74, A_75]: (r1_tarski(k4_xboole_0(C_73, B_74), k4_xboole_0(C_73, A_75)) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.12/2.28  tff(c_331, plain, (![A_75]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_3', A_75)) | ~r1_tarski(A_75, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_323])).
% 6.12/2.28  tff(c_5923, plain, (![B_303]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k4_xboole_0('#skF_4', B_303))) | ~r1_tarski(k4_xboole_0('#skF_4', B_303), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5885, c_331])).
% 6.12/2.28  tff(c_6022, plain, (![B_306]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k4_xboole_0('#skF_4', B_306))))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5923])).
% 6.12/2.28  tff(c_6039, plain, (![B_10]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_10))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_6022])).
% 6.12/2.28  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.12/2.28  tff(c_427, plain, (![A_87, B_88, C_89]: (k9_subset_1(A_87, B_88, C_89)=k3_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.12/2.28  tff(c_439, plain, (![B_88]: (k9_subset_1('#skF_3', B_88, '#skF_5')=k3_xboole_0(B_88, '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_427])).
% 6.12/2.28  tff(c_36, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.12/2.28  tff(c_441, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_36])).
% 6.12/2.28  tff(c_6489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6039, c_441])).
% 6.12/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.28  
% 6.12/2.28  Inference rules
% 6.12/2.28  ----------------------
% 6.12/2.28  #Ref     : 0
% 6.12/2.28  #Sup     : 1531
% 6.12/2.28  #Fact    : 0
% 6.12/2.28  #Define  : 0
% 6.12/2.28  #Split   : 4
% 6.12/2.28  #Chain   : 0
% 6.12/2.28  #Close   : 0
% 6.12/2.28  
% 6.12/2.28  Ordering : KBO
% 6.12/2.28  
% 6.12/2.28  Simplification rules
% 6.12/2.28  ----------------------
% 6.12/2.28  #Subsume      : 51
% 6.12/2.28  #Demod        : 370
% 6.12/2.28  #Tautology    : 372
% 6.12/2.28  #SimpNegUnit  : 8
% 6.12/2.28  #BackRed      : 4
% 6.12/2.28  
% 6.12/2.28  #Partial instantiations: 0
% 6.12/2.28  #Strategies tried      : 1
% 6.12/2.28  
% 6.12/2.28  Timing (in seconds)
% 6.12/2.28  ----------------------
% 6.12/2.28  Preprocessing        : 0.31
% 6.12/2.28  Parsing              : 0.16
% 6.12/2.28  CNF conversion       : 0.02
% 6.12/2.28  Main loop            : 1.21
% 6.12/2.28  Inferencing          : 0.36
% 6.12/2.28  Reduction            : 0.45
% 6.12/2.28  Demodulation         : 0.34
% 6.12/2.28  BG Simplification    : 0.05
% 6.12/2.28  Subsumption          : 0.26
% 6.12/2.28  Abstraction          : 0.06
% 6.12/2.28  MUC search           : 0.00
% 6.12/2.28  Cooper               : 0.00
% 6.12/2.28  Total                : 1.55
% 6.12/2.28  Index Insertion      : 0.00
% 6.12/2.28  Index Deletion       : 0.00
% 6.12/2.28  Index Matching       : 0.00
% 6.12/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
