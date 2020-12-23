%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 166 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 362 expanded)
%              Number of equality atoms :   35 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_8] : r1_tarski('#skF_6',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_46,plain,(
    m1_setfam_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    ! [A_18] :
      ( '#skF_4'(A_18) != k1_xboole_0
      | k3_tarski(A_18) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_53,plain,(
    ! [A_18] :
      ( '#skF_4'(A_18) != '#skF_6'
      | k3_tarski(A_18) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_42])).

tff(c_89,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,k3_tarski(B_30))
      | ~ m1_setfam_1(B_30,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_249,plain,(
    ! [A_57,A_58] :
      ( r1_tarski(A_57,'#skF_6')
      | ~ m1_setfam_1(A_58,A_57)
      | '#skF_4'(A_58) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_89])).

tff(c_262,plain,
    ( r1_tarski(u1_struct_0('#skF_5'),'#skF_6')
    | '#skF_4'('#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_249])).

tff(c_281,plain,(
    '#skF_4'('#skF_6') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_40,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | k3_tarski(A_18) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | k3_tarski(A_18) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_173,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_424,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_4'(A_76),B_77)
      | ~ r1_tarski(A_76,B_77)
      | k3_tarski(A_76) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_54,c_173])).

tff(c_20,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1208,plain,(
    ! [A_122,A_123] :
      ( r1_tarski('#skF_4'(A_122),A_123)
      | ~ r1_tarski(A_122,k1_zfmisc_1(A_123))
      | k3_tarski(A_122) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_424,c_20])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [A_9] :
      ( A_9 = '#skF_6'
      | ~ r1_tarski(A_9,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_18])).

tff(c_1229,plain,(
    ! [A_124] :
      ( '#skF_4'(A_124) = '#skF_6'
      | ~ r1_tarski(A_124,k1_zfmisc_1('#skF_6'))
      | k3_tarski(A_124) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1208,c_56])).

tff(c_1265,plain,
    ( '#skF_4'('#skF_6') = '#skF_6'
    | k3_tarski('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_57,c_1229])).

tff(c_1278,plain,(
    k3_tarski('#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_1265])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,k3_tarski(B_16))
      | ~ m1_setfam_1(B_16,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_135,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [B_16,A_15] :
      ( k3_tarski(B_16) = A_15
      | ~ r1_tarski(k3_tarski(B_16),A_15)
      | ~ m1_setfam_1(B_16,A_15) ) ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_1296,plain,(
    ! [A_15] :
      ( k3_tarski('#skF_6') = A_15
      | ~ r1_tarski('#skF_6',A_15)
      | ~ m1_setfam_1('#skF_6',A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_142])).

tff(c_1386,plain,(
    ! [A_126] :
      ( A_126 = '#skF_6'
      | ~ m1_setfam_1('#skF_6',A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1278,c_1296])).

tff(c_1407,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_1386])).

tff(c_36,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1414,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1407,c_36])).

tff(c_1418,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_59,c_1414])).

tff(c_1420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1418])).

tff(c_1421,plain,(
    r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1431,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1421,c_10])).

tff(c_1437,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1431])).

tff(c_1447,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1437,c_36])).

tff(c_1451,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_59,c_1447])).

tff(c_1453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.49  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.15/1.49  
% 3.15/1.49  %Foreground sorts:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Background operators:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Foreground operators:
% 3.15/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.15/1.49  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.15/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.49  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 3.15/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.49  
% 3.32/1.51  tff(f_98, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 3.32/1.51  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.32/1.51  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.32/1.51  tff(f_84, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 3.32/1.51  tff(f_56, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 3.32/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.32/1.51  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.32/1.51  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.32/1.51  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.32/1.51  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.32/1.51  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.51  tff(c_50, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.51  tff(c_44, plain, (k1_xboole_0='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.51  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.51  tff(c_59, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 3.32/1.51  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.51  tff(c_57, plain, (![A_8]: (r1_tarski('#skF_6', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 3.32/1.51  tff(c_46, plain, (m1_setfam_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.51  tff(c_42, plain, (![A_18]: ('#skF_4'(A_18)!=k1_xboole_0 | k3_tarski(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.32/1.51  tff(c_53, plain, (![A_18]: ('#skF_4'(A_18)!='#skF_6' | k3_tarski(A_18)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_42])).
% 3.32/1.51  tff(c_89, plain, (![A_29, B_30]: (r1_tarski(A_29, k3_tarski(B_30)) | ~m1_setfam_1(B_30, A_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.32/1.51  tff(c_249, plain, (![A_57, A_58]: (r1_tarski(A_57, '#skF_6') | ~m1_setfam_1(A_58, A_57) | '#skF_4'(A_58)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_53, c_89])).
% 3.32/1.51  tff(c_262, plain, (r1_tarski(u1_struct_0('#skF_5'), '#skF_6') | '#skF_4'('#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_46, c_249])).
% 3.32/1.51  tff(c_281, plain, ('#skF_4'('#skF_6')!='#skF_6'), inference(splitLeft, [status(thm)], [c_262])).
% 3.32/1.51  tff(c_40, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | k3_tarski(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.32/1.51  tff(c_54, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | k3_tarski(A_18)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 3.32/1.51  tff(c_173, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.51  tff(c_424, plain, (![A_76, B_77]: (r2_hidden('#skF_4'(A_76), B_77) | ~r1_tarski(A_76, B_77) | k3_tarski(A_76)='#skF_6')), inference(resolution, [status(thm)], [c_54, c_173])).
% 3.32/1.51  tff(c_20, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.32/1.51  tff(c_1208, plain, (![A_122, A_123]: (r1_tarski('#skF_4'(A_122), A_123) | ~r1_tarski(A_122, k1_zfmisc_1(A_123)) | k3_tarski(A_122)='#skF_6')), inference(resolution, [status(thm)], [c_424, c_20])).
% 3.32/1.51  tff(c_18, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.51  tff(c_56, plain, (![A_9]: (A_9='#skF_6' | ~r1_tarski(A_9, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_18])).
% 3.32/1.51  tff(c_1229, plain, (![A_124]: ('#skF_4'(A_124)='#skF_6' | ~r1_tarski(A_124, k1_zfmisc_1('#skF_6')) | k3_tarski(A_124)='#skF_6')), inference(resolution, [status(thm)], [c_1208, c_56])).
% 3.32/1.51  tff(c_1265, plain, ('#skF_4'('#skF_6')='#skF_6' | k3_tarski('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_57, c_1229])).
% 3.32/1.51  tff(c_1278, plain, (k3_tarski('#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_281, c_1265])).
% 3.32/1.51  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, k3_tarski(B_16)) | ~m1_setfam_1(B_16, A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.32/1.51  tff(c_135, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.51  tff(c_142, plain, (![B_16, A_15]: (k3_tarski(B_16)=A_15 | ~r1_tarski(k3_tarski(B_16), A_15) | ~m1_setfam_1(B_16, A_15))), inference(resolution, [status(thm)], [c_32, c_135])).
% 3.32/1.51  tff(c_1296, plain, (![A_15]: (k3_tarski('#skF_6')=A_15 | ~r1_tarski('#skF_6', A_15) | ~m1_setfam_1('#skF_6', A_15))), inference(superposition, [status(thm), theory('equality')], [c_1278, c_142])).
% 3.32/1.51  tff(c_1386, plain, (![A_126]: (A_126='#skF_6' | ~m1_setfam_1('#skF_6', A_126))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1278, c_1296])).
% 3.32/1.51  tff(c_1407, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_1386])).
% 3.32/1.51  tff(c_36, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.51  tff(c_1414, plain, (~v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1407, c_36])).
% 3.32/1.51  tff(c_1418, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_59, c_1414])).
% 3.32/1.51  tff(c_1420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1418])).
% 3.32/1.51  tff(c_1421, plain, (r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_262])).
% 3.32/1.51  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.51  tff(c_1431, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1421, c_10])).
% 3.32/1.51  tff(c_1437, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_1431])).
% 3.32/1.51  tff(c_1447, plain, (~v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1437, c_36])).
% 3.32/1.51  tff(c_1451, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_59, c_1447])).
% 3.32/1.51  tff(c_1453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1451])).
% 3.32/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.51  
% 3.32/1.51  Inference rules
% 3.32/1.51  ----------------------
% 3.32/1.51  #Ref     : 0
% 3.32/1.51  #Sup     : 326
% 3.32/1.51  #Fact    : 0
% 3.32/1.51  #Define  : 0
% 3.32/1.51  #Split   : 5
% 3.32/1.51  #Chain   : 0
% 3.32/1.51  #Close   : 0
% 3.32/1.51  
% 3.32/1.51  Ordering : KBO
% 3.32/1.51  
% 3.32/1.51  Simplification rules
% 3.32/1.51  ----------------------
% 3.32/1.51  #Subsume      : 73
% 3.32/1.51  #Demod        : 116
% 3.32/1.51  #Tautology    : 109
% 3.32/1.51  #SimpNegUnit  : 12
% 3.32/1.51  #BackRed      : 12
% 3.32/1.51  
% 3.32/1.51  #Partial instantiations: 0
% 3.32/1.51  #Strategies tried      : 1
% 3.32/1.51  
% 3.32/1.51  Timing (in seconds)
% 3.32/1.51  ----------------------
% 3.32/1.51  Preprocessing        : 0.30
% 3.32/1.51  Parsing              : 0.16
% 3.32/1.51  CNF conversion       : 0.02
% 3.32/1.51  Main loop            : 0.45
% 3.32/1.51  Inferencing          : 0.16
% 3.32/1.51  Reduction            : 0.13
% 3.32/1.51  Demodulation         : 0.09
% 3.32/1.51  BG Simplification    : 0.02
% 3.32/1.51  Subsumption          : 0.10
% 3.32/1.51  Abstraction          : 0.02
% 3.32/1.51  MUC search           : 0.00
% 3.32/1.51  Cooper               : 0.00
% 3.32/1.51  Total                : 0.78
% 3.32/1.51  Index Insertion      : 0.00
% 3.32/1.51  Index Deletion       : 0.00
% 3.32/1.51  Index Matching       : 0.00
% 3.32/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
