%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:55 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 113 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 341 expanded)
%              Number of equality atoms :   20 (  49 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_26,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_45,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_344,plain,(
    ! [B_66,A_67] :
      ( v2_tops_1(B_66,A_67)
      | k1_tops_1(A_67,B_66) != k1_xboole_0
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_351,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_344])).

tff(c_355,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_351])).

tff(c_356,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_355])).

tff(c_73,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_tops_1(A_41,B_42),B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_82,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_78])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_457,plain,(
    ! [A_74,B_75] :
      ( v3_pre_topc(k1_tops_1(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_462,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_457])).

tff(c_466,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_462])).

tff(c_47,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_57,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(B_37,C_36)
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_35,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_51,c_57])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [C_29] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_29
      | ~ v3_pre_topc(C_29,'#skF_1')
      | ~ r1_tarski(C_29,'#skF_2')
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_372,plain,(
    ! [C_69] :
      ( k1_xboole_0 = C_69
      | ~ v3_pre_topc(C_69,'#skF_1')
      | ~ r1_tarski(C_69,'#skF_2')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_44])).

tff(c_485,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ v3_pre_topc(A_77,'#skF_1')
      | ~ r1_tarski(A_77,'#skF_2')
      | ~ r1_tarski(A_77,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_8,c_372])).

tff(c_510,plain,(
    ! [A_78] :
      ( k1_xboole_0 = A_78
      | ~ v3_pre_topc(A_78,'#skF_1')
      | ~ r1_tarski(A_78,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_485])).

tff(c_513,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_466,c_510])).

tff(c_516,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_513])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_516])).

tff(c_519,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_520,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_525,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_28])).

tff(c_30,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_523,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_30])).

tff(c_32,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_527,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_32])).

tff(c_677,plain,(
    ! [A_100,B_101] :
      ( k1_tops_1(A_100,B_101) = k1_xboole_0
      | ~ v2_tops_1(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_687,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_677])).

tff(c_695,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_520,c_687])).

tff(c_990,plain,(
    ! [B_116,A_117,C_118] :
      ( r1_tarski(B_116,k1_tops_1(A_117,C_118))
      | ~ r1_tarski(B_116,C_118)
      | ~ v3_pre_topc(B_116,A_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_997,plain,(
    ! [B_116] :
      ( r1_tarski(B_116,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_116,'#skF_2')
      | ~ v3_pre_topc(B_116,'#skF_1')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_990])).

tff(c_1086,plain,(
    ! [B_124] :
      ( r1_tarski(B_124,k1_xboole_0)
      | ~ r1_tarski(B_124,'#skF_2')
      | ~ v3_pre_topc(B_124,'#skF_1')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_695,c_997])).

tff(c_1093,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_527,c_1086])).

tff(c_1100,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_523,c_1093])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1117,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1100,c_4])).

tff(c_1134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_519,c_1117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:04:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.47  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.47  
% 3.15/1.47  %Foreground sorts:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Background operators:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Foreground operators:
% 3.15/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.15/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.15/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.15/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.15/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.47  
% 3.32/1.48  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.32/1.48  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.32/1.48  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.32/1.48  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.32/1.48  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.48  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.32/1.48  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.32/1.48  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.32/1.48  tff(c_26, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_45, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 3.32/1.48  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_344, plain, (![B_66, A_67]: (v2_tops_1(B_66, A_67) | k1_tops_1(A_67, B_66)!=k1_xboole_0 | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.32/1.48  tff(c_351, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_344])).
% 3.32/1.48  tff(c_355, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_351])).
% 3.32/1.48  tff(c_356, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_45, c_355])).
% 3.32/1.48  tff(c_73, plain, (![A_41, B_42]: (r1_tarski(k1_tops_1(A_41, B_42), B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.32/1.48  tff(c_78, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_73])).
% 3.32/1.48  tff(c_82, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_78])).
% 3.32/1.48  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_457, plain, (![A_74, B_75]: (v3_pre_topc(k1_tops_1(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.48  tff(c_462, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_457])).
% 3.32/1.48  tff(c_466, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_462])).
% 3.32/1.48  tff(c_47, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.48  tff(c_51, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_47])).
% 3.32/1.48  tff(c_57, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(B_37, C_36) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.48  tff(c_60, plain, (![A_35]: (r1_tarski(A_35, u1_struct_0('#skF_1')) | ~r1_tarski(A_35, '#skF_2'))), inference(resolution, [status(thm)], [c_51, c_57])).
% 3.32/1.48  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.48  tff(c_44, plain, (![C_29]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_29 | ~v3_pre_topc(C_29, '#skF_1') | ~r1_tarski(C_29, '#skF_2') | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_372, plain, (![C_69]: (k1_xboole_0=C_69 | ~v3_pre_topc(C_69, '#skF_1') | ~r1_tarski(C_69, '#skF_2') | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_45, c_44])).
% 3.32/1.48  tff(c_485, plain, (![A_77]: (k1_xboole_0=A_77 | ~v3_pre_topc(A_77, '#skF_1') | ~r1_tarski(A_77, '#skF_2') | ~r1_tarski(A_77, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_372])).
% 3.32/1.48  tff(c_510, plain, (![A_78]: (k1_xboole_0=A_78 | ~v3_pre_topc(A_78, '#skF_1') | ~r1_tarski(A_78, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_485])).
% 3.32/1.48  tff(c_513, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_466, c_510])).
% 3.32/1.48  tff(c_516, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_82, c_513])).
% 3.32/1.48  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_516])).
% 3.32/1.48  tff(c_519, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 3.32/1.48  tff(c_520, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 3.32/1.48  tff(c_28, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_525, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_28])).
% 3.32/1.48  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_523, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_30])).
% 3.32/1.48  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.48  tff(c_527, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_520, c_32])).
% 3.32/1.48  tff(c_677, plain, (![A_100, B_101]: (k1_tops_1(A_100, B_101)=k1_xboole_0 | ~v2_tops_1(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.32/1.48  tff(c_687, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_677])).
% 3.32/1.48  tff(c_695, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_520, c_687])).
% 3.32/1.48  tff(c_990, plain, (![B_116, A_117, C_118]: (r1_tarski(B_116, k1_tops_1(A_117, C_118)) | ~r1_tarski(B_116, C_118) | ~v3_pre_topc(B_116, A_117) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.32/1.48  tff(c_997, plain, (![B_116]: (r1_tarski(B_116, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_116, '#skF_2') | ~v3_pre_topc(B_116, '#skF_1') | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_990])).
% 3.32/1.48  tff(c_1086, plain, (![B_124]: (r1_tarski(B_124, k1_xboole_0) | ~r1_tarski(B_124, '#skF_2') | ~v3_pre_topc(B_124, '#skF_1') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_695, c_997])).
% 3.32/1.48  tff(c_1093, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_527, c_1086])).
% 3.32/1.48  tff(c_1100, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_525, c_523, c_1093])).
% 3.32/1.48  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.48  tff(c_1117, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1100, c_4])).
% 3.32/1.48  tff(c_1134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_519, c_1117])).
% 3.32/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.48  
% 3.32/1.48  Inference rules
% 3.32/1.48  ----------------------
% 3.32/1.48  #Ref     : 0
% 3.32/1.48  #Sup     : 240
% 3.32/1.48  #Fact    : 0
% 3.32/1.48  #Define  : 0
% 3.32/1.48  #Split   : 13
% 3.32/1.48  #Chain   : 0
% 3.32/1.48  #Close   : 0
% 3.32/1.48  
% 3.32/1.48  Ordering : KBO
% 3.32/1.48  
% 3.32/1.48  Simplification rules
% 3.32/1.48  ----------------------
% 3.32/1.48  #Subsume      : 75
% 3.32/1.48  #Demod        : 151
% 3.32/1.48  #Tautology    : 69
% 3.32/1.48  #SimpNegUnit  : 10
% 3.32/1.48  #BackRed      : 5
% 3.32/1.48  
% 3.32/1.48  #Partial instantiations: 0
% 3.32/1.48  #Strategies tried      : 1
% 3.32/1.48  
% 3.32/1.48  Timing (in seconds)
% 3.32/1.48  ----------------------
% 3.32/1.49  Preprocessing        : 0.31
% 3.32/1.49  Parsing              : 0.16
% 3.32/1.49  CNF conversion       : 0.02
% 3.32/1.49  Main loop            : 0.41
% 3.32/1.49  Inferencing          : 0.14
% 3.32/1.49  Reduction            : 0.12
% 3.32/1.49  Demodulation         : 0.08
% 3.32/1.49  BG Simplification    : 0.02
% 3.32/1.49  Subsumption          : 0.10
% 3.32/1.49  Abstraction          : 0.02
% 3.32/1.49  MUC search           : 0.00
% 3.32/1.49  Cooper               : 0.00
% 3.32/1.49  Total                : 0.75
% 3.32/1.49  Index Insertion      : 0.00
% 3.32/1.49  Index Deletion       : 0.00
% 3.32/1.49  Index Matching       : 0.00
% 3.32/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
