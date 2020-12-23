%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:39 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   65 (  80 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 121 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_104,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_78,plain,
    ( r1_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6'))
    | r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_102,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_238,plain,(
    ~ r1_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_72])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1231,plain,(
    ! [A_136,B_137] :
      ( k4_xboole_0(A_136,B_137) = k3_subset_1(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1251,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_1231])).

tff(c_28,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_185,plain,(
    ! [A_70,B_71] :
      ( k2_xboole_0(A_70,B_71) = B_71
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_196,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_102,c_185])).

tff(c_432,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_xboole_0(A_88,B_89)
      | ~ r1_xboole_0(A_88,k2_xboole_0(B_89,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_453,plain,(
    ! [A_91] :
      ( r1_xboole_0(A_91,'#skF_5')
      | ~ r1_xboole_0(A_91,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_432])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_464,plain,(
    ! [A_94] :
      ( r1_xboole_0('#skF_5',A_94)
      | ~ r1_xboole_0(A_94,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_453,c_12])).

tff(c_468,plain,(
    ! [A_24] : r1_xboole_0('#skF_5',k4_xboole_0(A_24,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_464])).

tff(c_1266,plain,(
    r1_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1251,c_468])).

tff(c_1279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_1266])).

tff(c_1281,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1280,plain,(
    r1_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2303,plain,(
    ! [A_217,B_218] :
      ( k4_xboole_0(A_217,B_218) = k3_subset_1(A_217,B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2323,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_2303])).

tff(c_62,plain,(
    ! [A_44,B_45] : k6_subset_1(A_44,B_45) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    ! [A_39,B_40] : m1_subset_1(k6_subset_1(A_39,B_40),k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_79,plain,(
    ! [A_39,B_40] : m1_subset_1(k4_xboole_0(A_39,B_40),k1_zfmisc_1(A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56])).

tff(c_2338,plain,(
    m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2323,c_79])).

tff(c_2156,plain,(
    ! [A_206,B_207] :
      ( k3_subset_1(A_206,k3_subset_1(A_206,B_207)) = B_207
      | ~ m1_subset_1(B_207,k1_zfmisc_1(A_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2168,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_2156])).

tff(c_3237,plain,(
    ! [B_264,A_265,C_266] :
      ( r1_tarski(B_264,k3_subset_1(A_265,C_266))
      | ~ r1_xboole_0(B_264,C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(A_265))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(A_265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3256,plain,(
    ! [B_264] :
      ( r1_tarski(B_264,'#skF_6')
      | ~ r1_xboole_0(B_264,k3_subset_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(k3_subset_1('#skF_4','#skF_6'),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_264,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2168,c_3237])).

tff(c_5454,plain,(
    ! [B_320] :
      ( r1_tarski(B_320,'#skF_6')
      | ~ r1_xboole_0(B_320,k3_subset_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_320,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_3256])).

tff(c_5489,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1280,c_5454])).

tff(c_5509,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5489])).

tff(c_5511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1281,c_5509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:22:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.18  
% 5.73/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 5.73/2.18  
% 5.73/2.18  %Foreground sorts:
% 5.73/2.18  
% 5.73/2.18  
% 5.73/2.18  %Background operators:
% 5.73/2.18  
% 5.73/2.18  
% 5.73/2.18  %Foreground operators:
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.73/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.73/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.73/2.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.73/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.73/2.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.73/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.73/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.73/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.73/2.18  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.73/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.73/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.73/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.73/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.73/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.73/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.73/2.18  
% 5.73/2.19  tff(f_132, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 5.73/2.19  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.73/2.19  tff(f_72, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.73/2.19  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.73/2.19  tff(f_66, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.73/2.19  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.73/2.19  tff(f_113, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.73/2.19  tff(f_104, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.73/2.19  tff(f_111, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.73/2.19  tff(f_122, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 5.73/2.19  tff(c_78, plain, (r1_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6')) | r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.73/2.19  tff(c_102, plain, (r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 5.73/2.19  tff(c_72, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.73/2.19  tff(c_238, plain, (~r1_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_72])).
% 5.73/2.19  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.73/2.19  tff(c_1231, plain, (![A_136, B_137]: (k4_xboole_0(A_136, B_137)=k3_subset_1(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.73/2.19  tff(c_1251, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_1231])).
% 5.73/2.19  tff(c_28, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.73/2.19  tff(c_185, plain, (![A_70, B_71]: (k2_xboole_0(A_70, B_71)=B_71 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.73/2.19  tff(c_196, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_102, c_185])).
% 5.73/2.19  tff(c_432, plain, (![A_88, B_89, C_90]: (r1_xboole_0(A_88, B_89) | ~r1_xboole_0(A_88, k2_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.73/2.19  tff(c_453, plain, (![A_91]: (r1_xboole_0(A_91, '#skF_5') | ~r1_xboole_0(A_91, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_432])).
% 5.73/2.19  tff(c_12, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.73/2.19  tff(c_464, plain, (![A_94]: (r1_xboole_0('#skF_5', A_94) | ~r1_xboole_0(A_94, '#skF_6'))), inference(resolution, [status(thm)], [c_453, c_12])).
% 5.73/2.19  tff(c_468, plain, (![A_24]: (r1_xboole_0('#skF_5', k4_xboole_0(A_24, '#skF_6')))), inference(resolution, [status(thm)], [c_28, c_464])).
% 5.73/2.19  tff(c_1266, plain, (r1_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1251, c_468])).
% 5.73/2.19  tff(c_1279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_1266])).
% 5.73/2.19  tff(c_1281, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 5.73/2.19  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.73/2.19  tff(c_1280, plain, (r1_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_78])).
% 5.73/2.19  tff(c_2303, plain, (![A_217, B_218]: (k4_xboole_0(A_217, B_218)=k3_subset_1(A_217, B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(A_217)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.73/2.19  tff(c_2323, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_2303])).
% 5.73/2.19  tff(c_62, plain, (![A_44, B_45]: (k6_subset_1(A_44, B_45)=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.73/2.19  tff(c_56, plain, (![A_39, B_40]: (m1_subset_1(k6_subset_1(A_39, B_40), k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.73/2.19  tff(c_79, plain, (![A_39, B_40]: (m1_subset_1(k4_xboole_0(A_39, B_40), k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56])).
% 5.73/2.19  tff(c_2338, plain, (m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2323, c_79])).
% 5.73/2.19  tff(c_2156, plain, (![A_206, B_207]: (k3_subset_1(A_206, k3_subset_1(A_206, B_207))=B_207 | ~m1_subset_1(B_207, k1_zfmisc_1(A_206)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.73/2.19  tff(c_2168, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_68, c_2156])).
% 5.73/2.19  tff(c_3237, plain, (![B_264, A_265, C_266]: (r1_tarski(B_264, k3_subset_1(A_265, C_266)) | ~r1_xboole_0(B_264, C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(A_265)) | ~m1_subset_1(B_264, k1_zfmisc_1(A_265)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.73/2.19  tff(c_3256, plain, (![B_264]: (r1_tarski(B_264, '#skF_6') | ~r1_xboole_0(B_264, k3_subset_1('#skF_4', '#skF_6')) | ~m1_subset_1(k3_subset_1('#skF_4', '#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_264, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2168, c_3237])).
% 5.73/2.19  tff(c_5454, plain, (![B_320]: (r1_tarski(B_320, '#skF_6') | ~r1_xboole_0(B_320, k3_subset_1('#skF_4', '#skF_6')) | ~m1_subset_1(B_320, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2338, c_3256])).
% 5.73/2.19  tff(c_5489, plain, (r1_tarski('#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_1280, c_5454])).
% 5.73/2.19  tff(c_5509, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5489])).
% 5.73/2.19  tff(c_5511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1281, c_5509])).
% 5.73/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.19  
% 5.73/2.19  Inference rules
% 5.73/2.19  ----------------------
% 5.73/2.19  #Ref     : 0
% 5.73/2.19  #Sup     : 1409
% 5.73/2.19  #Fact    : 0
% 5.73/2.19  #Define  : 0
% 5.73/2.19  #Split   : 3
% 5.73/2.19  #Chain   : 0
% 5.73/2.19  #Close   : 0
% 5.73/2.19  
% 5.73/2.19  Ordering : KBO
% 5.73/2.19  
% 5.73/2.19  Simplification rules
% 5.73/2.19  ----------------------
% 5.73/2.19  #Subsume      : 47
% 5.73/2.19  #Demod        : 871
% 5.73/2.19  #Tautology    : 991
% 5.73/2.19  #SimpNegUnit  : 6
% 5.73/2.19  #BackRed      : 4
% 5.73/2.19  
% 5.73/2.19  #Partial instantiations: 0
% 5.73/2.19  #Strategies tried      : 1
% 5.73/2.19  
% 5.73/2.19  Timing (in seconds)
% 5.73/2.19  ----------------------
% 5.73/2.20  Preprocessing        : 0.40
% 5.73/2.20  Parsing              : 0.20
% 5.73/2.20  CNF conversion       : 0.03
% 5.73/2.20  Main loop            : 1.00
% 5.73/2.20  Inferencing          : 0.32
% 5.73/2.20  Reduction            : 0.39
% 5.73/2.20  Demodulation         : 0.31
% 5.73/2.20  BG Simplification    : 0.04
% 5.73/2.20  Subsumption          : 0.17
% 5.73/2.20  Abstraction          : 0.05
% 5.73/2.20  MUC search           : 0.00
% 5.73/2.20  Cooper               : 0.00
% 5.73/2.20  Total                : 1.42
% 5.73/2.20  Index Insertion      : 0.00
% 5.73/2.20  Index Deletion       : 0.00
% 5.73/2.20  Index Matching       : 0.00
% 5.73/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
