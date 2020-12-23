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
% DateTime   : Thu Dec  3 09:55:36 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   57 (  75 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 116 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_28,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_41,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_77,plain,(
    ! [B_35,A_36] :
      ( r2_hidden(B_35,A_36)
      | ~ m1_subset_1(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [B_35,A_7] :
      ( r1_tarski(B_35,A_7)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_85,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(B_37,A_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_81])).

tff(c_94,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_133,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k3_subset_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_146,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_133])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_4])).

tff(c_157,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_150])).

tff(c_173,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k3_subset_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    ! [B_35,A_7] :
      ( r1_tarski(B_35,A_7)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_7)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_81])).

tff(c_184,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k3_subset_1(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_173,c_84])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( r2_hidden(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [B_39,A_40] :
      ( m1_subset_1(B_39,A_40)
      | ~ r2_hidden(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_105,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_101])).

tff(c_280,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_subset_1(A_67,B_68,C_69) = k2_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_332,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,B_75,C_76) = k2_xboole_0(B_75,C_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74))
      | ~ r1_tarski(C_76,A_74) ) ),
    inference(resolution,[status(thm)],[c_105,c_280])).

tff(c_346,plain,(
    ! [C_77] :
      ( k4_subset_1('#skF_3','#skF_4',C_77) = k2_xboole_0('#skF_4',C_77)
      | ~ r1_tarski(C_77,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_332])).

tff(c_548,plain,(
    ! [B_91] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_91)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_184,c_346])).

tff(c_571,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_548])).

tff(c_582,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_571])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:21:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.49  
% 2.88/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.49  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.88/1.49  
% 2.88/1.49  %Foreground sorts:
% 2.88/1.49  
% 2.88/1.49  
% 2.88/1.49  %Background operators:
% 2.88/1.49  
% 2.88/1.49  
% 2.88/1.49  %Foreground operators:
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.88/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.88/1.49  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.88/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.88/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.88/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.49  
% 2.88/1.51  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.88/1.51  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.88/1.51  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.88/1.51  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.88/1.51  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.88/1.51  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.88/1.51  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.88/1.51  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.88/1.51  tff(f_72, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.88/1.51  tff(c_28, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.51  tff(c_38, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.88/1.51  tff(c_41, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.88/1.51  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.88/1.51  tff(c_34, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.88/1.51  tff(c_77, plain, (![B_35, A_36]: (r2_hidden(B_35, A_36) | ~m1_subset_1(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.51  tff(c_8, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.51  tff(c_81, plain, (![B_35, A_7]: (r1_tarski(B_35, A_7) | ~m1_subset_1(B_35, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_77, c_8])).
% 2.88/1.51  tff(c_85, plain, (![B_37, A_38]: (r1_tarski(B_37, A_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)))), inference(negUnitSimplification, [status(thm)], [c_34, c_81])).
% 2.88/1.51  tff(c_94, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_85])).
% 2.88/1.51  tff(c_133, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k3_subset_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.88/1.51  tff(c_146, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_133])).
% 2.88/1.51  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.51  tff(c_150, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_146, c_4])).
% 2.88/1.51  tff(c_157, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_150])).
% 2.88/1.51  tff(c_173, plain, (![A_51, B_52]: (m1_subset_1(k3_subset_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.88/1.51  tff(c_84, plain, (![B_35, A_7]: (r1_tarski(B_35, A_7) | ~m1_subset_1(B_35, k1_zfmisc_1(A_7)))), inference(negUnitSimplification, [status(thm)], [c_34, c_81])).
% 2.88/1.51  tff(c_184, plain, (![A_51, B_52]: (r1_tarski(k3_subset_1(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_173, c_84])).
% 2.88/1.51  tff(c_10, plain, (![C_11, A_7]: (r2_hidden(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.51  tff(c_95, plain, (![B_39, A_40]: (m1_subset_1(B_39, A_40) | ~r2_hidden(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.51  tff(c_101, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(resolution, [status(thm)], [c_10, c_95])).
% 2.88/1.51  tff(c_105, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(negUnitSimplification, [status(thm)], [c_34, c_101])).
% 2.88/1.51  tff(c_280, plain, (![A_67, B_68, C_69]: (k4_subset_1(A_67, B_68, C_69)=k2_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.51  tff(c_332, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, B_75, C_76)=k2_xboole_0(B_75, C_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)) | ~r1_tarski(C_76, A_74))), inference(resolution, [status(thm)], [c_105, c_280])).
% 2.88/1.51  tff(c_346, plain, (![C_77]: (k4_subset_1('#skF_3', '#skF_4', C_77)=k2_xboole_0('#skF_4', C_77) | ~r1_tarski(C_77, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_332])).
% 2.88/1.51  tff(c_548, plain, (![B_91]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_91))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_184, c_346])).
% 2.88/1.51  tff(c_571, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_548])).
% 2.88/1.51  tff(c_582, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_571])).
% 2.88/1.51  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_582])).
% 2.88/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.51  
% 2.88/1.51  Inference rules
% 2.88/1.51  ----------------------
% 2.88/1.51  #Ref     : 0
% 2.88/1.51  #Sup     : 116
% 2.88/1.51  #Fact    : 0
% 2.88/1.51  #Define  : 0
% 2.88/1.51  #Split   : 1
% 2.88/1.51  #Chain   : 0
% 2.88/1.51  #Close   : 0
% 2.88/1.51  
% 2.88/1.51  Ordering : KBO
% 2.88/1.51  
% 2.88/1.51  Simplification rules
% 2.88/1.51  ----------------------
% 2.88/1.51  #Subsume      : 14
% 2.88/1.51  #Demod        : 10
% 2.88/1.51  #Tautology    : 39
% 2.88/1.51  #SimpNegUnit  : 20
% 2.88/1.51  #BackRed      : 0
% 2.88/1.51  
% 2.88/1.51  #Partial instantiations: 0
% 2.88/1.51  #Strategies tried      : 1
% 2.88/1.51  
% 2.88/1.51  Timing (in seconds)
% 2.88/1.51  ----------------------
% 2.88/1.51  Preprocessing        : 0.29
% 2.88/1.51  Parsing              : 0.15
% 2.88/1.51  CNF conversion       : 0.02
% 2.88/1.51  Main loop            : 0.38
% 2.88/1.51  Inferencing          : 0.16
% 2.88/1.51  Reduction            : 0.09
% 2.88/1.51  Demodulation         : 0.06
% 2.88/1.51  BG Simplification    : 0.02
% 2.88/1.51  Subsumption          : 0.08
% 2.88/1.51  Abstraction          : 0.03
% 2.88/1.51  MUC search           : 0.00
% 2.88/1.51  Cooper               : 0.00
% 2.88/1.51  Total                : 0.70
% 2.88/1.51  Index Insertion      : 0.00
% 2.88/1.51  Index Deletion       : 0.00
% 2.88/1.51  Index Matching       : 0.00
% 2.88/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
