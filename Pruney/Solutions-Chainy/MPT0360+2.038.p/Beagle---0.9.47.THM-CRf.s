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
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 170 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_53,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_67,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(B_29,A_30)
      | ~ m1_subset_1(B_29,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    ! [B_29,A_4] :
      ( r1_tarski(B_29,A_4)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_4))
      | v1_xboole_0(k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_75,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(B_31,A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_71])).

tff(c_84,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_75])).

tff(c_106,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84,c_106])).

tff(c_131,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( r2_hidden(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [B_33,A_34] :
      ( m1_subset_1(B_33,A_34)
      | ~ r2_hidden(B_33,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [C_8,A_4] :
      ( m1_subset_1(C_8,k1_zfmisc_1(A_4))
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_95,plain,(
    ! [C_8,A_4] :
      ( m1_subset_1(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_91])).

tff(c_36,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_389,plain,(
    ! [C_72,A_73,B_74] :
      ( r1_tarski(C_72,k3_subset_1(A_73,B_74))
      | ~ r1_tarski(B_74,k3_subset_1(A_73,C_72))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_403,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_389])).

tff(c_413,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_403])).

tff(c_414,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_417,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_414])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_417])).

tff(c_426,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_425,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_465,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_76,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_425,c_2])).

tff(c_24,plain,(
    ! [A_11] : k1_subset_1(A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k1_subset_1(A_17) = B_18
      | ~ r1_tarski(B_18,k3_subset_1(A_17,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41,plain,(
    ! [B_18,A_17] :
      ( k1_xboole_0 = B_18
      | ~ r1_tarski(B_18,k3_subset_1(A_17,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_482,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_465,c_41])).

tff(c_496,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_426,c_482])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n019.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 10:01:22 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.25  
% 2.54/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.54/1.25  
% 2.54/1.25  %Foreground sorts:
% 2.54/1.25  
% 2.54/1.25  
% 2.54/1.25  %Background operators:
% 2.54/1.25  
% 2.54/1.25  
% 2.54/1.25  %Foreground operators:
% 2.54/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.54/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.25  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.54/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.25  
% 2.54/1.26  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 2.54/1.26  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.54/1.26  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.54/1.26  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.54/1.26  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.54/1.26  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.54/1.26  tff(f_53, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.54/1.26  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.54/1.26  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.26  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.26  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.26  tff(c_26, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.54/1.26  tff(c_67, plain, (![B_29, A_30]: (r2_hidden(B_29, A_30) | ~m1_subset_1(B_29, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.26  tff(c_4, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.26  tff(c_71, plain, (![B_29, A_4]: (r1_tarski(B_29, A_4) | ~m1_subset_1(B_29, k1_zfmisc_1(A_4)) | v1_xboole_0(k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_67, c_4])).
% 2.54/1.26  tff(c_75, plain, (![B_31, A_32]: (r1_tarski(B_31, A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)))), inference(negUnitSimplification, [status(thm)], [c_26, c_71])).
% 2.54/1.26  tff(c_84, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_75])).
% 2.54/1.26  tff(c_106, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.26  tff(c_123, plain, (![A_42]: (r1_tarski(A_42, '#skF_3') | ~r1_tarski(A_42, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_106])).
% 2.54/1.26  tff(c_131, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_123])).
% 2.54/1.26  tff(c_6, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.26  tff(c_85, plain, (![B_33, A_34]: (m1_subset_1(B_33, A_34) | ~r2_hidden(B_33, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.26  tff(c_91, plain, (![C_8, A_4]: (m1_subset_1(C_8, k1_zfmisc_1(A_4)) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(resolution, [status(thm)], [c_6, c_85])).
% 2.54/1.26  tff(c_95, plain, (![C_8, A_4]: (m1_subset_1(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(negUnitSimplification, [status(thm)], [c_26, c_91])).
% 2.54/1.26  tff(c_36, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.26  tff(c_389, plain, (![C_72, A_73, B_74]: (r1_tarski(C_72, k3_subset_1(A_73, B_74)) | ~r1_tarski(B_74, k3_subset_1(A_73, C_72)) | ~m1_subset_1(C_72, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.54/1.26  tff(c_403, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_389])).
% 2.54/1.26  tff(c_413, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_403])).
% 2.54/1.26  tff(c_414, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_413])).
% 2.54/1.26  tff(c_417, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_95, c_414])).
% 2.54/1.26  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_417])).
% 2.54/1.26  tff(c_426, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_413])).
% 2.54/1.26  tff(c_425, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_413])).
% 2.54/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.26  tff(c_465, plain, (![A_76]: (r1_tarski(A_76, k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski(A_76, '#skF_5'))), inference(resolution, [status(thm)], [c_425, c_2])).
% 2.54/1.26  tff(c_24, plain, (![A_11]: (k1_subset_1(A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.54/1.26  tff(c_32, plain, (![A_17, B_18]: (k1_subset_1(A_17)=B_18 | ~r1_tarski(B_18, k3_subset_1(A_17, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.54/1.26  tff(c_41, plain, (![B_18, A_17]: (k1_xboole_0=B_18 | ~r1_tarski(B_18, k3_subset_1(A_17, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_32])).
% 2.54/1.26  tff(c_482, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_465, c_41])).
% 2.54/1.26  tff(c_496, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_426, c_482])).
% 2.54/1.26  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_496])).
% 2.54/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.26  
% 2.54/1.26  Inference rules
% 2.54/1.26  ----------------------
% 2.54/1.26  #Ref     : 0
% 2.54/1.26  #Sup     : 105
% 2.54/1.26  #Fact    : 0
% 2.54/1.26  #Define  : 0
% 2.54/1.26  #Split   : 4
% 2.54/1.26  #Chain   : 0
% 2.54/1.26  #Close   : 0
% 2.54/1.26  
% 2.54/1.26  Ordering : KBO
% 2.54/1.26  
% 2.54/1.26  Simplification rules
% 2.54/1.26  ----------------------
% 2.54/1.26  #Subsume      : 24
% 2.54/1.26  #Demod        : 26
% 2.54/1.26  #Tautology    : 18
% 2.54/1.26  #SimpNegUnit  : 6
% 2.54/1.26  #BackRed      : 0
% 2.54/1.26  
% 2.54/1.26  #Partial instantiations: 0
% 2.54/1.26  #Strategies tried      : 1
% 2.54/1.26  
% 2.54/1.26  Timing (in seconds)
% 2.54/1.26  ----------------------
% 2.54/1.27  Preprocessing        : 0.31
% 2.54/1.27  Parsing              : 0.16
% 2.54/1.27  CNF conversion       : 0.02
% 2.54/1.27  Main loop            : 0.29
% 2.54/1.27  Inferencing          : 0.11
% 2.54/1.27  Reduction            : 0.08
% 2.54/1.27  Demodulation         : 0.05
% 2.54/1.27  BG Simplification    : 0.02
% 2.54/1.27  Subsumption          : 0.07
% 2.54/1.27  Abstraction          : 0.01
% 2.54/1.27  MUC search           : 0.00
% 2.54/1.27  Cooper               : 0.00
% 2.54/1.27  Total                : 0.63
% 2.54/1.27  Index Insertion      : 0.00
% 2.54/1.27  Index Deletion       : 0.00
% 2.54/1.27  Index Matching       : 0.00
% 2.54/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
